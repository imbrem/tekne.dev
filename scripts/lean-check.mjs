#!/usr/bin/env node
/**
 * Build every Lean development under lean/.
 *
 *   pnpm lean            # build them all
 *   pnpm lean --list     # just say what would be built
 *
 * A "development" is any directory holding a lakefile. They are built rather
 * than merely elaborated because `lake build` is what actually reports errors
 * and `sorry` warnings across a whole library.
 */

import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, readdirSync, readFileSync } from 'node:fs';
import { join, dirname, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const LEAN = join(ROOT, 'lean');

/** Directories under lean/ that contain a lakefile, not descending into .lake. */
function findProjects(dir, found = []) {
	if (!existsSync(dir)) return found;
	const entries = readdirSync(dir, { withFileTypes: true });
	if (entries.some((e) => e.isFile() && /^lakefile\.(toml|lean)$/.test(e.name))) {
		found.push(dir);
		return found; // a lakefile marks the root; nested ones are dependencies
	}
	for (const e of entries) {
		if (e.isDirectory() && e.name !== '.lake' && !e.name.startsWith('.')) {
			findProjects(join(dir, e.name), found);
		}
	}
	return found;
}

const projects = findProjects(LEAN);

if (projects.length === 0) {
	console.log('no Lean developments found under lean/');
	process.exit(0);
}

if (process.argv.includes('--list')) {
	for (const p of projects) console.log(relative(ROOT, p));
	process.exit(0);
}

try {
	execFileSync('sh', ['-c', 'command -v lake'], { stdio: 'ignore' });
} catch {
	console.error('`lake` is not on PATH — run inside `nix develop`, which provides elan.');
	process.exit(1);
}

let failed = 0;
for (const project of projects) {
	const name = relative(ROOT, project);
	console.log(`\n=== ${name} ===`);

	// Without the prebuilt oleans, `lake build` would compile Mathlib from
	// source: hours rather than seconds. Fetch them if they are absent.
	const manifest = join(project, 'lake-manifest.json');
	const mathlibBuilt = existsSync(
		join(project, '.lake', 'packages', 'mathlib', '.lake', 'build', 'lib')
	);
	const usesMathlib =
		existsSync(manifest) &&
		JSON.parse(readFileSync(manifest, 'utf8')).packages?.some((p) => p.name === 'mathlib');

	if (usesMathlib && !mathlibBuilt) {
		console.log('mathlib oleans missing — fetching the cache first');
		const got = spawnSync('lake', ['exe', 'cache', 'get'], { cwd: project, stdio: 'inherit' });
		if (got.status !== 0) {
			console.error(`${name}: could not fetch the Mathlib cache`);
			failed++;
			continue;
		}
	}

	const res = spawnSync('lake', ['build'], { cwd: project, stdio: 'inherit' });
	if (res.status !== 0) failed++;
}

console.log();
if (failed) {
	console.error(`${failed} of ${projects.length} development(s) failed`);
	process.exit(1);
}
console.log(`${projects.length} development(s) built cleanly`);
