/**
 * Invariants of the content-addressed store.
 *
 * These are pure — no build, no server — so they run in milliseconds and can be
 * used as a fast pre-commit check on their own:
 *
 *     node --test tests/cas.test.mjs
 */

import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join, extname, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { blake3 } from '@noble/hashes/blake3.js';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const STORE = join(ROOT, 'static', 'cas');
const manifest = JSON.parse(readFileSync(join(ROOT, 'static', 'cas.json'), 'utf8'));

const runCas = (...args) =>
	execFileSync('node', [join(ROOT, 'scripts', 'cas.mjs'), ...args], {
		cwd: ROOT,
		encoding: 'utf8'
	});

describe('content-addressed store', () => {
	test('every object is named by the BLAKE3 of its own bytes', () => {
		const files = existsSync(STORE) ? readdirSync(STORE) : [];
		assert.ok(files.length > 0, 'store is empty — expected at least one object');
		for (const file of files) {
			const actual = Buffer.from(blake3(readFileSync(join(STORE, file)))).toString('hex');
			assert.equal(actual, file, `${file} does not hash to its own name`);
		}
	});

	test('objects are bare hashes: identity carries no type', () => {
		for (const file of readdirSync(STORE)) {
			assert.equal(extname(file), '', `${file} has an extension; type belongs to names`);
		}
	});

	test('every name resolves to an object that exists', () => {
		for (const [name, n] of Object.entries(manifest.names)) {
			assert.ok(manifest.objects[n.hash], `${name} points at absent object ${n.hash}`);
			assert.ok(existsSync(join(STORE, n.hash)), `${name} points at missing file ${n.hash}`);
		}
	});

	test('every name carries the semantics the object deliberately lacks', () => {
		for (const [name, n] of Object.entries(manifest.names)) {
			assert.ok(n.mediaType, `${name} has no mediaType`);
			assert.ok(n.filename, `${name} has no filename`);
		}
	});

	test('a name binds to exactly one object', () => {
		// The manifest keys names, so duplicates are impossible by construction —
		// this guards the shape rather than the data, in case it ever becomes a list.
		for (const [name, n] of Object.entries(manifest.names)) {
			assert.equal(typeof n.hash, 'string', `${name} should bind a single hash`);
		}
	});

	test('history never references an object that has been dropped', () => {
		// Retired bindings are the archive's backbone: if an object named by
		// history disappears, a past URL becomes unrecoverable.
		for (const h of manifest.history) {
			assert.ok(
				existsSync(join(STORE, h.hash)),
				`history references ${h.hash} for ${h.name}, but that object is gone`
			);
		}
	});

	test('`cas verify` agrees', () => {
		assert.match(runCas('verify'), /object\(s\) verified/);
	});

	test('`cas check` agrees firebase.json matches the manifest', () => {
		assert.match(runCas('check'), /firebase\.json agrees with cas\.json/);
	});
});
