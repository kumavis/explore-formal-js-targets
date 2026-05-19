// Driver for the Agda capability examples.
// Same shape as the Idris2 one: set the host capability on globalThis
// before loading the compiled Agda module (which runs its embedded `main`
// as a side effect of being require()'d).

import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

globalThis.__hostLog = (n) => process.stdout.write('  [host log] ' + n + '\n');

// Agda's per-module emission means we need NODE_PATH pointing at the dir
// so sibling jAgda.X.js requires resolve.
process.env.NODE_PATH = __dirname;
require('node:module').Module._initPaths();

require(path.join(__dirname, 'jAgda.Caps.js'));
