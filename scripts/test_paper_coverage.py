#!/usr/bin/env python3
"""Offline negative checks of the paper-profile structural acceptance gate."""

from copy import deepcopy
import json
from pathlib import Path

from verify import require_paper_coverage


def main():
    root = Path(__file__).resolve().parents[1]
    baseline = [json.loads((root / name).read_text()) for name in
                ['paper_inventory.json', 'implementation_map.json', 'equation_map.json']]
    require_paper_coverage(*baseline)
    print('PASS complete paper preflight')
    for case in ['missing_named', 'missing_sup', 'missing_equation',
                 'duplicate_equation', 'false_complete', 'unverified_sup']:
        inventory, ledger, equations = deepcopy(baseline)
        if case == 'missing_named':
            ledger['complete_named_results'].pop(next(iter(ledger['complete_named_results'])))
        elif case == 'missing_sup':
            ledger['complete_supplementary_results'].pop('SUP-25')
        elif case == 'missing_equation':
            equations['equations'].pop()
        elif case == 'duplicate_equation':
            equations['equations'][-1] = deepcopy(equations['equations'][0])
        elif case == 'false_complete':
            equations['complete'] = False
        elif case == 'unverified_sup':
            inventory['supplementary_claims'][0]['status'] = 'mapped_not_verified'
        try:
            require_paper_coverage(inventory, ledger, equations)
        except RuntimeError as error:
            print(f'PASS reject {case}: {error}')
        else:
            raise RuntimeError(f'Incomplete paper fixture was accepted: {case}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
