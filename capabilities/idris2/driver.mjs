// Driver for the Idris2 capability examples.
// The Idris2 program reaches `globalThis.__hostLog` via %foreign, so the
// driver has to install it *before* the program runs. Idris2's --cg node
// output is a self-running script (not a module), so we read it as text,
// strip the shebang, and eval it after the global is in place.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// The capability the verified program will reach for.
globalThis.__hostLog = (n) => process.stdout.write('  [host log] ' + n + '\n');

// Run the Idris2 executable as a script in this process.
const src = fs.readFileSync(path.join(__dirname, 'build/exec/caps'), 'utf8')
  .replace(/^#![^\n]*\n/, '');
eval(src);
