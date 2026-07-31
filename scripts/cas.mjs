#!/usr/bin/env node
/**
 * Content-addressed store for immutable assets.
 *
 * Objects live at static/cas/<blake3>.<ext> and are committed to the repo, so
 * the repository *is* the store — there is no build step that could drift from
 * it, and `npm run preview` serves exactly what deploys.
 *
 * The manifest lives at static/cas.json, deliberately OUTSIDE static/cas/: that
 * directory is served with `immutable` cache headers, and the manifest is the
 * one thing here that changes.
 *
 * The manifest separates two things that are easy to conflate:
 *
 *   objects  — immutable content, keyed by hash. Append-only.
 *   names    — mutable pointers into that content. Exactly one hash each.
 *   history  — every name→hash binding that has ever been retired, with dates.
 *
 * Names are served as 302 redirects to the object, never as rewrites. Two
 * reasons, both load-bearing:
 *
 *   - Dedup. A redirect makes the client fetch the /cas/ URL, so every name
 *     pointing at the same bytes shares one cache entry, in the browser and at
 *     the CDN. A rewrite would serve those bytes *at* the name, giving each
 *     name its own independently-cached copy of the same content.
 *   - Revisability. A name is mutable, the content it points at is not.
 *     Browsers cache a 301 more or less permanently, so a 301 would pin the
 *     name to one hash forever for anyone who had already followed it.
 *
 * Usage:
 *   node scripts/cas.mjs add <file> [--name <alias>]... [--title <title>]
 *   node scripts/cas.mjs ls
 *   node scripts/cas.mjs verify
 *   node scripts/cas.mjs aliases
 *   node scripts/cas.mjs check
 */

import { blake3 } from '@noble/hashes/blake3.js';
import { readFileSync, writeFileSync, existsSync, mkdirSync, readdirSync } from 'node:fs';
import { join, extname, dirname, basename } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const STORE = join(ROOT, 'static', 'cas');
const MANIFEST = join(ROOT, 'static', 'cas.json');
const FIREBASE = join(ROOT, 'firebase.json');

// Informational only — Firebase derives the response Content-Type from the
// file extension, which is exactly why objects keep theirs.
const MEDIA_TYPES = {
	'.pdf': 'application/pdf',
	'.wasm': 'application/wasm',
	'.png': 'image/png',
	'.jpg': 'image/jpeg',
	'.jpeg': 'image/jpeg',
	'.svg': 'image/svg+xml',
	'.json': 'application/json',
	'.txt': 'text/plain',
	'.md': 'text/markdown',
	'.zip': 'application/zip',
	'.sqlite3': 'application/vnd.sqlite3'
};

const hashOf = (bytes) => Buffer.from(blake3(bytes)).toString('hex');
const today = () => new Date().toISOString().slice(0, 10);
const normalise = (name) => (name.startsWith('/') ? name : `/${name}`);

function loadManifest() {
	if (!existsSync(MANIFEST)) {
		return { algorithm: 'blake3-256', encoding: 'hex', objects: {}, names: {}, history: [] };
	}
	const m = JSON.parse(readFileSync(MANIFEST, 'utf8'));
	return { names: {}, history: [], ...m };
}

function saveManifest(m) {
	const sortKeys = (o) =>
		Object.fromEntries(Object.entries(o).sort(([a], [b]) => a.localeCompare(b)));
	const out = {
		algorithm: m.algorithm,
		encoding: m.encoding,
		objects: sortKeys(m.objects),
		names: sortKeys(m.names),
		history: m.history
	};
	writeFileSync(MANIFEST, JSON.stringify(out, null, '\t') + '\n');
}

/** Point `name` at `hash`, retiring any previous binding into history. */
function bind(m, name, hash) {
	const previous = m.names[name];
	if (previous === hash) return;
	if (previous) {
		// When the binding was made: the end of the name's prior stint if it had
		// one, else the date the object itself entered the store.
		const from =
			m.history.findLast?.((h) => h.name === name && h.hash === previous)?.until ??
			m.objects[previous]?.added ??
			null;
		m.history.push({ name, hash: previous, from, until: today() });
		console.log(`  rebound ${name}: ${previous.slice(0, 12)}… -> ${hash.slice(0, 12)}…`);
	}
	m.names[name] = hash;
}

function add(args) {
	const file = args.find((a) => !a.startsWith('--'));
	if (!file) throw new Error('usage: cas.mjs add <file> [--name <alias>]... [--title <title>]');

	const names = [];
	let title = null;
	for (let i = 0; i < args.length; i++) {
		if (args[i] === '--name') names.push(normalise(args[++i]));
		if (args[i] === '--title') title = args[++i];
	}

	const bytes = readFileSync(file);
	const hash = hashOf(bytes);
	const ext = extname(file).toLowerCase();
	const stored = `${hash}${ext}`;
	const target = join(STORE, stored);

	const m = loadManifest();

	if (!existsSync(target)) {
		mkdirSync(STORE, { recursive: true });
		writeFileSync(target, bytes);
		console.log(`stored: ${stored} (${bytes.length} bytes)`);
	} else {
		console.log(`already stored: ${stored}`);
	}

	// Written whenever absent rather than only on first store, so the manifest
	// is always reconstructible from the objects on disk — deleting cas.json and
	// re-adding must converge, not half-populate.
	m.objects[hash] = {
		ext,
		path: `/cas/${stored}`,
		mediaType: MEDIA_TYPES[ext] ?? 'application/octet-stream',
		size: bytes.length,
		originalName: basename(file),
		added: m.objects[hash]?.added ?? today(),
		...(m.objects[hash]?.title ? { title: m.objects[hash].title } : {}),
		...(title ? { title } : {})
	};

	for (const name of names) bind(m, name, hash);
	saveManifest(m);

	console.log(`  url:   /cas/${stored}`);
	const pointing = Object.entries(m.names)
		.filter(([, h]) => h === hash)
		.map(([n]) => n);
	if (pointing.length) console.log(`  names: ${pointing.join(', ')}`);
	if (names.length) console.log(`\nRun \`npm run cas -- check\` after updating firebase.json.`);
}

function ls() {
	const m = loadManifest();
	const entries = Object.entries(m.objects);
	if (!entries.length) return console.log('(store is empty)');
	for (const [hash, o] of entries) {
		const pointing = Object.entries(m.names)
			.filter(([, h]) => h === hash)
			.map(([n]) => n);
		console.log(`${hash}${o.ext}`);
		console.log(`  ${o.title ?? o.originalName}  ${o.size} bytes  added ${o.added}`);
		if (pointing.length) console.log(`  names: ${pointing.join(', ')}`);
	}
	if (m.history.length) {
		console.log(`\nretired bindings:`);
		for (const h of m.history) {
			console.log(`  ${h.name} -> ${h.hash.slice(0, 12)}…  until ${h.until}`);
		}
	}
}

/**
 * Re-hash every stored object and confirm its content still matches its name.
 * That is the entire invariant of the store, so it is worth asserting cheaply.
 * Also flags objects on disk the manifest forgot, manifest entries with no
 * object, and names pointing into thin air.
 */
function verify() {
	const m = loadManifest();
	let bad = 0;

	const onDisk = existsSync(STORE) ? readdirSync(STORE) : [];
	for (const file of onDisk) {
		const expected = basename(file, extname(file));
		const actual = hashOf(readFileSync(join(STORE, file)));
		if (actual !== expected) {
			console.error(`CORRUPT ${file}\n  content hashes to ${actual}`);
			bad++;
		} else if (!m.objects[expected]) {
			console.error(`UNTRACKED ${file} (on disk but absent from cas.json)`);
			bad++;
		} else {
			console.log(`ok ${file}`);
		}
	}

	for (const [hash, o] of Object.entries(m.objects)) {
		if (!existsSync(join(STORE, `${hash}${o.ext}`))) {
			console.error(`MISSING ${hash}${o.ext} (in cas.json but not on disk)`);
			bad++;
		}
	}

	for (const [name, hash] of Object.entries(m.names)) {
		if (!m.objects[hash]) {
			console.error(`DANGLING name ${name} -> ${hash} (no such object)`);
			bad++;
		}
	}

	if (bad) {
		console.error(`\n${bad} problem(s)`);
		process.exit(1);
	}
	console.log(`\n${onDisk.length} object(s) verified, ${Object.keys(m.names).length} name(s)`);
}

/** The firebase.json redirect entries implied by the name table. */
function redirectsFromManifest(m) {
	return Object.entries(m.names).map(([name, hash]) => ({
		source: name,
		destination: `/cas/${hash}${m.objects[hash].ext}`,
		type: 302
	}));
}

function aliases() {
	console.log(JSON.stringify(redirectsFromManifest(loadManifest()), null, '\t'));
}

/**
 * firebase.json is hand-maintained (it also holds the blog's 301s), so the name
 * table is not generated into it. Instead, assert the two agree — otherwise a
 * rebound name silently keeps serving the old object.
 */
function check() {
	const m = loadManifest();
	const want = redirectsFromManifest(m);
	const have = JSON.parse(readFileSync(FIREBASE, 'utf8')).hosting.redirects ?? [];
	const bySource = new Map(have.map((r) => [r.source, r]));
	let bad = 0;

	for (const w of want) {
		const got = bySource.get(w.source);
		if (!got) {
			console.error(`MISSING redirect for ${w.source} -> ${w.destination}`);
			bad++;
		} else if (got.destination !== w.destination) {
			console.error(
				`STALE ${w.source}\n  firebase.json -> ${got.destination}\n  cas.json      -> ${w.destination}`
			);
			bad++;
		} else if (got.type !== 302) {
			console.error(`${w.source} is a ${got.type}; CAS names must be 302 (see header comment)`);
			bad++;
		}
	}

	const casDestinations = have.filter((r) => r.destination.startsWith('/cas/'));
	for (const r of casDestinations) {
		if (!m.names[r.source]) {
			console.error(`ORPHAN redirect ${r.source} -> ${r.destination} (no such name in cas.json)`);
			bad++;
		}
	}

	if (bad) {
		console.error(`\n${bad} problem(s) — run \`npm run cas -- aliases\` for the expected entries`);
		process.exit(1);
	}
	console.log(`firebase.json agrees with cas.json (${want.length} name(s))`);
}

const [cmd, ...args] = process.argv.slice(2);
const commands = { add, ls, verify, aliases, check };
if (!commands[cmd]) {
	console.error('usage: cas.mjs <add|ls|verify|aliases|check> [...]');
	process.exit(1);
}
commands[cmd](args);
