"""Check V2 layout, exact mathematical preservation, numbering and Lean reuse.

All mathematical reference data are frozen locally. The optional protected
workspace comparison reads the old papers/proofs without modifying them.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def inspect_build(directory, pdf):
    log = (directory/'main.log').read_text(errors='replace')
    warnings = re.findall(r'^.*(?:Warning|Overfull|Underfull|Missing character|^!).*$', log, re.M)
    assert not warnings, warnings
    subprocess.run(['pdftotext', '-layout', str(pdf), str(directory/'main.txt')], check=True)
    subprocess.run(['pdftotext', '-bbox', str(pdf), str(directory/'main-bbox.html')], check=True)
    # Poppler may emit XML-forbidden control characters for legacy math glyphs.
    # Remove only those controls in the parser input; retain the raw extraction.
    bbox = (directory/'main-bbox.html').read_text()
    bbox = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]', '', bbox)
    pages = ET.fromstring(bbox).findall('.//{*}page')
    assert pages
    outside, empty = [], []
    for number, page in enumerate(pages, 1):
        width, height = float(page.get('width')), float(page.get('height'))
        words = page.findall('.//{*}word')
        if len(words) < 5:
            empty.append(number)
        for word in words:
            if (float(word.get('xMin')) < 0 or float(word.get('yMin')) < 0
                    or float(word.get('xMax')) > width or float(word.get('yMax')) > height):
                outside.append((number, word.text))
    assert not outside and not empty, (outside, empty)
    font_output = subprocess.check_output(['pdffonts', str(pdf)], text=True)
    (directory/'fonts.txt').write_text(font_output)
    rows = font_output.splitlines()[2:]
    assert rows and all(row.split()[-5] == 'yes' for row in rows), font_output
    assert not any('Type 3' in row for row in rows), font_output
    info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
    (directory/'pdfinfo.txt').write_text(info)
    return {'pages':len(pages), 'warnings':warnings, 'empty_pages':empty,
            'text_outside_media_box':outside, 'all_fonts_embedded':True,
            'type3_fonts':False, 'font_entries':len(rows)}


def main():
    baseline=json.loads((ROOT/'editorial/math_baseline.json').read_text())
    sources=[ROOT/name for name in baseline['section_files']]
    body='\n'.join(p.read_text() for p in sources)
    abstract=(ROOT/'abstract.tex').read_text()
    all_tex='\n'.join((ROOT/n).read_text() for n in ['main.tex','metadata.tex','abstract.tex'])+'\n'+body
    equations=dict(re.findall(r'\\begin\{equation\}\\label\{eq:([^}]+)\}(.*?)\\end\{equation\}',body,re.S))
    assert len(equations)==198 and equations=={k:v['latex'] for k,v in baseline['equations'].items()}
    statements={}
    for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}',body,re.S):
        key=re.search(r'\\label\{([^}]+)\}',m[0])[1]
        assert key not in statements
        statements[key]={'kind':m[1],'text':m[0]}
    assert len(statements)==28
    assert {k:v['text'] for k,v in statements.items()}=={k:v['latex'] for k,v in baseline['statements'].items()}
    proofs=re.findall(r'\\begin\{proof\}.*?\\end\{proof\}',body,re.S)
    assert sorted(sha256(x.encode()).hexdigest() for x in proofs)==baseline['proof_sha256']
    assert len(proofs)==body.count(r'\end{proof}')==24
    summaries=json.loads((ROOT/'editorial/front_summary_claims.json').read_text())
    summary_pattern=r'% BEGIN VERIFIED OVERVIEW (\w+)\n(.*?)% END VERIFIED OVERVIEW \1'
    found=list(re.finditer(summary_pattern,body,re.S))
    assert {m[1] for m in found}==set(summaries['blocks'])
    for m in found:
        expected=summaries['blocks'][m[1]]
        assert m[0]==expected['latex'] and sha256(m[0].encode()).hexdigest()==expected['sha256']
        assert set(expected['dependencies'])<=set(baseline['statements'])
        assert set(expected['source_equations'])<=set(baseline['equations'])
    unchanged_body=re.sub(summary_pattern,'',body,flags=re.S)
    inline=re.findall(r'(?<!\$)\$([^$\n]+)\$(?!\$)',unchanged_body)
    assert Counter(inline)==Counter(baseline['inline_math_multiset'])
    assert sum(len(re.findall(r'\\\[.*?\\\]',m[2],re.S)) for m in found)==4
    main_source=(ROOT/'main.tex').read_text()
    assert r'\documentclass[11pt,letterpaper]' in main_source and 'hidelinks' in main_source
    assert r'\numberwithin{equation}{section}' in main_source
    labels=re.findall(r'\\label\{([^}]+)\}',all_tex)
    refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',all_tex)
    assert len(labels)==len(set(labels)) and set(refs)<=set(labels)
    assert not re.search(r'ZZ(?:TOKEN|DISPLAY|FIGURE)|<a id=|\*\*|∎|/home/|\.\./',all_tex)
    assert len(re.findall(r'(?m)^\\section\{',body))==6
    assert body.index(r'\label{thm-sharp}')<body.index(r'\label{sec:2}')
    assert body.index(r'\label{sec:8}')<body.index(r'\label{sec:eq-stability}')<body.index(r'\label{sec:2.3}')
    assert len(re.findall(r'\\includegraphics',body))==2
    assert body.count(r'\begin{table}')==1
    for name in re.findall(r'\\(?:input|includegraphics)(?:\[[^\]]*\])?\{([^}]+)\}',all_tex):
        p=ROOT/name
        if not p.suffix:p=p.with_suffix('.tex')
        assert p.is_file() and p.resolve().is_relative_to(ROOT),name
    ad=re.findall(r'\\\[(.*?)\\\]',abstract,re.S)
    assert len(ad)==1
    compact=re.sub(r'\s','',ad[0])
    for expected in [r'w(K\capH)\leR_nw(K)',r'R_1=\frac12',r'R_n=\frac12\left(\fracn{n-1}\right)^{(n-1)/2}\quad(n\ge2)']:
        assert expected in compact,expected
    assert 'formally verified in Lean 4 using mathlib' in abstract
    citations=set()
    for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',all_tex):citations.update(group.split(','))
    bibkeys=set(re.findall(r'@\w+\{([^,]+),',(ROOT/'references.bib').read_text()))
    bbl=(ROOT/'main.bbl').read_text()
    bblkeys=set(re.findall(r'\\bibitem(?:\[[\s\S]*?\])?\{([^}]+)\}',bbl))
    assert citations==bibkeys==bblkeys and len(bibkeys)==19
    assert 'Longfei Zhou, Haijun Zou, and Tianhao Liu.' in bbl and 'arXiv:2609.28447' in bbl
    printed=dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}',(ROOT/'build/main.aux').read_text()))
    emap=[];smap=[];expected_numbers={}
    previous=json.loads((ROOT/'editorial/pre_main_version_optimization.json').read_text())['previous_numbering']
    previous_numbers={row['stable_label']:row['v2_number'] for row in previous['equations']}
    for section,path in enumerate(sources,1):
        keys=re.findall(r'\\begin\{equation\}\\label\{eq:([^}]+)\}',path.read_text())
        for index,key in enumerate(keys,1):expected_numbers[key]=str(section)+'.'+str(index)
    for old,content in equations.items():
        current=expected_numbers[old]
        assert printed['eq:'+old]==current,(old,printed['eq:'+old],current)
        emap.append({'stable_label':'eq:'+old,'original_equation':old,'previous_v2_number':previous_numbers['eq:'+old],'v2_number':current,'formula_sha256':sha256(content.encode()).hexdigest(),'lean_declarations':baseline['equations'][old]['lean_declarations'],'formal_correspondence':baseline['equations'][old]['formal_correspondence']})
    for i,(key,item) in enumerate(statements.items(),1):
        assert printed[key]==str(i),(key,printed[key],i)
        old=baseline['statements'][key]
        smap.append({'stable_label':key,'original_statement':old['old_name'],'v2_statement':item['kind'].title()+' '+str(i),'lean_declarations':old['lean_declarations'],'statement_sha256':old['sha256']})
    assert printed['fig:1']==printed['tab:main-results']=='1' and printed['fig:2']=='2'
    numbering={'scope':'Printed numbering changes only; stable labels and mathematical statements are preserved.','statements':smap,'equations':emap,'sections':{k:v for k,v in printed.items() if k.startswith('sec:')}}
    (ROOT/'editorial/numbering_map.json').write_text(json.dumps(numbering,indent=2)+'\n')
    protected=json.loads((ROOT/'editorial/protected_sources.json').read_text());checked=[]
    for name,h in protected.items():
        p=ROOT.parent/name
        if p.exists():
            assert digest(p)==h,'Protected source modified: '+name
            checked.append(name)
    if (ROOT.parent/'formal_proof').is_dir() and (ROOT.parent/'latex_for_arXiv_second_paper').is_dir():
        assert len(checked)==len(protected),'Protected file disappeared'
    pdf=inspect_build(ROOT/'build',ROOT/'main.pdf')
    assert digest(ROOT/'main.pdf')==digest(ROOT/'build/main.pdf')
    assert digest(ROOT/'main.bbl')==digest(ROOT/'build/main.bbl')
    assert '612 x 792 pts (letter)' in (ROOT/'build/pdfinfo.txt').read_text()
    fonts=(ROOT/'build/fonts.txt').read_text()
    assert all(font in fonts for font in ['CMR10','CMR17','CMR12'])
    inputs=[ROOT/n for n in ['main.tex','metadata.tex','abstract.tex']]+sources+[ROOT/'references.bib',ROOT/'main.bbl']+sorted((ROOT/'figures').glob('*.pdf'))
    result={'scope':'V2 mathematical preservation, renumbering, read-only Lean reuse and typesetting check; no new Lean proof or kernel run.',
      'numbered_sections':6,'named_statements':28,'numbered_equations':198,'proof_environments':24,'original_body_inline_expressions':len(inline),
      'body_inline_expressions':len(re.findall(r'(?<!\$)\$([^$\n]+)\$(?!\$)',body)),
      'abstract_display_equations':1,'introductory_summary_displays':4,'introductory_summaries':'Existing results with explicit domains and unchanged constants; see editorial/front_summary_claims.json','overview_tables':1,'figures':2,'bibliography_entries':19,
      'all_statement_bodies_identical':True,'all_numbered_equations_identical':True,'all_proof_bodies_identical':True,'original_body_inline_multiset_identical_after_separating_summaries':True,
      'all_labels_unique':True,'all_cross_references_resolved':True,'formal_inventory_statements_identical':baseline['formal_inventory_statements_equal'],
      'protected_files_checked':len(checked),'protected_files_total':len(protected),'lean_rebuild_performed':False,'numbering_map':'editorial/numbering_map.json',
      'pdf':pdf,'input_sha256':{str(p.relative_to(ROOT)):digest(p) for p in inputs},'pdf_sha256':digest(ROOT/'main.pdf')}
    (ROOT/'build/validation.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=['# Statement correspondence: reference-style V2','','All mathematical statements are preserved; this table changes only their printed locations and numbers. The existing Lean project is read-only and retains its original mapping.','','| Original paper | V2 | Stable label | Existing Lean declaration(s) |','| --- | --- | --- | --- |']
    for row in smap:
        lines.append('| '+row['original_statement']+' | '+row['v2_statement']+' | `'+row['stable_label']+'` | '+'; '.join('`'+n+'`' for n in row['lean_declarations'])+' |')
    lines+=['','All 198 equation-number correspondences and section locations are in [numbering_map.json](editorial/numbering_map.json). The formalization remains based on the same stable theorem/equation identifiers. The abstract, introductory summaries and overview table restate existing verified results; their assumptions and correspondences are recorded in editorial/front_summary_claims.json.']
    (ROOT/'theorem_map.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='input_sha256'},indent=2))


if __name__=='__main__':main()
