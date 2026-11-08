// Render every math span of the generated chapters with the KaTeX that Verso vendors (throwOnError).
// usage (from blueprint/): node check_math.mjs [DIR]
import { readFileSync, readdirSync } from 'node:fs';
import { createRequire } from 'node:module';
const require = createRequire(import.meta.url);
const katex = require('./.lake/packages/verso/vendored-js/katex/katex.min.js');
const dir = (process.argv[2] ?? 'OspOddDeformationsBlueprint/Chapters') + '/';
let n = 0, bad = 0;
for (const f of readdirSync(dir).filter(x => x.endsWith('.lean'))) {
  const t = readFileSync(dir + f, 'utf8');
  for (const m of t.matchAll(/(\$\$?)`([^`]*)`/g)) {
    n++;
    try { katex.renderToString(m[2], { displayMode: m[1] === '$$', throwOnError: true }); }
    catch (e) { bad++; console.log(`${f}: ${e.message}\n   ${m[2].slice(0, 120)}`); }
  }
}
console.log(`check_math: ${n} math spans, ${bad} rendering errors`);
process.exit(bad ? 1 : 0);
