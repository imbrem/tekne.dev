#!/usr/bin/env node
/**
 * Content-addressed store for immutable assets.
 *
 * The store holds *bytes*, keyed only by BLAKE3 hash:
 *
 *     static/cas/<hash>   ->   /cas/<hash>
 *
 * No extension, no media type, no filename. `/cas/<hash>` means "give me these
 * bytes" and nothing else. Objects are committed to the repo, so the repository
 * *is* the store — nothing generates it, so nothing can drift from it, and
 * `pnpm preview` serves exactly what deploys.
 *
 * Everything else — media type, download filename, human-readable title — is
 * the business of a *name*, not of the object:
 *
 *     objects  — immutable bytes, keyed by hash. Append-only, untyped.
 *     names    — mutable pointers carrying the semantics. One hash each.
 *     history  — every name->hash binding retired so far, with dates.
 *
 * Names are served as REWRITES plus a per-name header rule, not as redirects.
 * That is forced by how Firebase resolves headers, which was measured, not
 * assumed:
 *
 *   - Header rules match the *request* path. So a rule on the name can set
 *     Content-Type and Content-Disposition, while /cas/** stays untyped.
 *   - A 302 cannot: the final response comes from /cas/<hash> and inherits its
 *     (absent) type, so no redirect-based alias can ever render inline.
 *   - A rewrite alone cannot either: the `.pdf` in the request path does not
 *     imply a type. The header rule is doing the work.
 *
 * The cost of a rewrite over a redirect is deduplication: the alias URL caches
 * its own copy of the bytes rather than converging on /cas/<hash>. Aliases are
 * few and human-facing; anything referencing content by hash still converges.
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

// Used to give a *name* its Content-Type, inferred from the name's own
// extension. Objects have no media type; only names do.
const MEDIA_TYPES = {
	'.pdf': 'application/pdf',
	'.wasm': 'application/wasm',
	'.png': 'image/png',
	'.jpg': 'image/jpeg',
	'.jpeg': 'image/jpeg',
	'.svg': 'image/svg+xml',
	'.json': 'application/json',
	'.txt': 'text/plain; charset=utf-8',
	'.md': 'text/markdown; charset=utf-8',
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
	return { names: {}, history: [], ...JSON.parse(readFileSync(MANIFEST, 'utf8')) };
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
	const previous = m.names[name]?.hash;
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

	const ext = extname(name).toLowerCase();
	m.names[name] = {
		hash,
		mediaType: MEDIA_TYPES[ext] ?? 'application/octet-stream',
		filename: basename(name),
		...(m.names[name]?.disposition ? { disposition: m.names[name].disposition } : {})
	};
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
	const target = join(STORE, hash);

	const m = loadManifest();

	if (!existsSync(target)) {
		mkdirSync(STORE, { recursive: true });
		writeFileSync(target, bytes);
		console.log(`stored: ${hash} (${bytes.length} bytes)`);
	} else {
		console.log(`already stored: ${hash}`);
	}

	// Written whenever absent rather than only on first store, so the manifest is
	// always reconstructible from the objects on disk — deleting cas.json and
	// re-adding must converge, not half-populate.
	m.objects[hash] = {
		path: `/cas/${hash}`,
		size: bytes.length,
		originalName: basename(file),
		added: m.objects[hash]?.added ?? today(),
		...(m.objects[hash]?.title ? { title: m.objects[hash].title } : {}),
		...(title ? { title } : {})
	};

	for (const name of names) bind(m, name, hash);
	saveManifest(m);

	console.log(`  url:   /cas/${hash}`);
	const pointing = Object.keys(m.names).filter((n) => m.names[n].hash === hash);
	if (pointing.length) console.log(`  names: ${pointing.join(', ')}`);
	if (names.length) console.log(`\nRun \`pnpm cas -- check\` after updating firebase.json.`);
}

function ls() {
	const m = loadManifest();
	const entries = Object.entries(m.objects);
	if (!entries.length) return console.log('(store is empty)');
	for (const [hash, o] of entries) {
		console.log(hash);
		console.log(`  ${o.title ?? o.originalName}  ${o.size} bytes  added ${o.added}`);
		for (const n of Object.keys(m.names).filter((n) => m.names[n].hash === hash)) {
			console.log(`  name: ${n}  (${m.names[n].mediaType})`);
		}
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
		if (extname(file)) {
			console.error(`EXTENSION ${file} (objects are bare hashes; type belongs to names)`);
			bad++;
			continue;
		}
		const actual = hashOf(readFileSync(join(STORE, file)));
		if (actual !== file) {
			console.error(`CORRUPT ${file}\n  content hashes to ${actual}`);
			bad++;
		} else if (!m.objects[file]) {
			console.error(`UNTRACKED ${file} (on disk but absent from cas.json)`);
			bad++;
		} else {
			console.log(`ok ${file}`);
		}
	}

	for (const hash of Object.keys(m.objects)) {
		if (!existsSync(join(STORE, hash))) {
			console.error(`MISSING ${hash} (in cas.json but not on disk)`);
			bad++;
		}
	}

	for (const [name, n] of Object.entries(m.names)) {
		if (!m.objects[n.hash]) {
			console.error(`DANGLING name ${name} -> ${n.hash} (no such object)`);
			bad++;
		}
	}

	if (bad) {
		console.error(`\n${bad} problem(s)`);
		process.exit(1);
	}
	console.log(`\n${onDisk.length} object(s) verified, ${Object.keys(m.names).length} name(s)`);
}

/** The firebase.json rewrites and header rules implied by the name table. */
function hostingFor(m) {
	const rewrites = Object.entries(m.names).map(([name, n]) => ({
		source: name,
		destination: `/cas/${n.hash}`
	}));
	const headers = Object.entries(m.names).map(([name, n]) => ({
		source: name,
		headers: [
			{ key: 'Content-Type', value: n.mediaType },
			{
				key: 'Content-Disposition',
				value: `${n.disposition ?? 'inline'}; filename="${n.filename}"`
			}
		]
	}));
	return { rewrites, headers };
}

function aliases() {
	console.log(JSON.stringify(hostingFor(loadManifest()), null, '\t'));
}

/**
 * firebase.json is hand-maintained (it also holds the blog's 301s), so the name
 * table is not generated into it. Instead, assert the two agree — otherwise a
 * rebound name silently keeps serving the old object, or loses its type.
 */
function check() {
	const m = loadManifest();
	const want = hostingFor(m);
	const fb = JSON.parse(readFileSync(FIREBASE, 'utf8')).hosting;
	const haveRewrites = new Map((fb.rewrites ?? []).map((r) => [r.source, r]));
	const haveHeaders = new Map((fb.headers ?? []).map((h) => [h.source, h]));
	let bad = 0;

	for (const w of want.rewrites) {
		const got = haveRewrites.get(w.source);
		if (!got) {
			console.error(`MISSING rewrite ${w.source} -> ${w.destination}`);
			bad++;
		} else if (got.destination !== w.destination) {
			console.error(
				`STALE rewrite ${w.source}\n  firebase.json -> ${got.destination}\n  cas.json      -> ${w.destination}`
			);
			bad++;
		}
	}

	for (const w of want.headers) {
		const got = haveHeaders.get(w.source);
		const flat = (h) => JSON.stringify((h?.headers ?? []).map((x) => [x.key, x.value]).sort());
		if (!got) {
			console.error(`MISSING header rule for ${w.source} (name would serve untyped)`);
			bad++;
		} else if (flat(got) !== flat(w)) {
			console.error(`STALE header rule ${w.source}\n  want ${flat(w)}\n  have ${flat(got)}`);
			bad++;
		}
	}

	for (const r of fb.rewrites ?? []) {
		if (r.destination.startsWith('/cas/') && !m.names[r.source]) {
			console.error(`ORPHAN rewrite ${r.source} -> ${r.destination} (no such name in cas.json)`);
			bad++;
		}
	}

	// A CAS name must never be a redirect: the response would come from
	// /cas/<hash> and inherit its lack of a type.
	for (const r of fb.redirects ?? []) {
		if (r.destination.startsWith('/cas/')) {
			console.error(`REDIRECT ${r.source} -> ${r.destination}; CAS names must be rewrites`);
			bad++;
		}
	}

	if (bad) {
		console.error(`\n${bad} problem(s) — run \`pnpm cas -- aliases\` for the expected entries`);
		process.exit(1);
	}
	console.log(`firebase.json agrees with cas.json (${want.rewrites.length} name(s))`);
}

const [cmd, ...args] = process.argv.slice(2);
const commands = { add, ls, verify, aliases, check };
if (!commands[cmd]) {
	console.error('usage: cas.mjs <add|ls|verify|aliases|check> [...]');
	process.exit(1);
}
commands[cmd](args);
