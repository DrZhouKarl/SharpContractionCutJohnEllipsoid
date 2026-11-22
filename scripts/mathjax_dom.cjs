// Optional offline MathJax check. Requires jsdom and a local MathJax 2 tree.
const fs = require('fs');
let jsdom;
try { jsdom = require('jsdom'); }
catch (_) {
  // Debian packages live in this shared directory; non-system Node may not
  // include it in the default module search path.
  process.env.NODE_PATH = [process.env.NODE_PATH, '/usr/share/nodejs'].filter(Boolean).join(require('path').delimiter);
  require('module').Module._initPaths();
  jsdom = require('jsdom');
}
const { JSDOM, ResourceLoader, VirtualConsole } = jsdom;
class OfflineLoader extends ResourceLoader {
  fetch(url, options) {
    if (!url.startsWith('file://')) throw new Error('Network resource rejected: ' + url);
    return super.fetch(url, options);
  }
}
const filename = process.argv[2];
const messages = [];
const vc = new VirtualConsole();
vc.on('jsdomError', e => messages.push(e.message));
const dom = new JSDOM(fs.readFileSync(filename, 'utf8'), {
  url: 'file://' + filename, resources: new OfflineLoader(),
  runScripts: 'dangerously', pretendToBeVisual: true, virtualConsole: vc
});
const started = Date.now();
const interval = setInterval(() => {
  const value = dom.window.document.getElementById('math-check-result').textContent;
  if (value !== 'PENDING') {
    clearInterval(interval);
    process.stdout.write(value + '\n');
    dom.window.close();
  } else if (Date.now() - started > 60000) {
    clearInterval(interval);
    process.stderr.write('MathJax did not finish: ' + JSON.stringify(messages) + '\n');
    dom.window.close();
    process.exitCode = 1;
  }
}, 100);
