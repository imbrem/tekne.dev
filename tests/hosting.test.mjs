/**
 * Hosting behaviour, asserted against the real Firebase hosting emulator.
 *
 * This exists because `vite preview` ignores firebase.json entirely, so the
 * whole redirect/rewrite/header layer was previously unverifiable without
 * deploying. It went wrong once in a way that was invisible from a browser:
 * every extensionless URL 404'd and served the empty SPA shell, which then
 * hydrated client-side and rendered the right page. The site looked perfect
 * while serving 404s and no content to crawlers for about a year.
 *
 * Hence the shape of these assertions: check the STATUS CODE and the SERVED
 * BYTES, never "does it look right".
 *
 * Requires `firebase` on PATH — run inside `nix develop`.
 */

import { test, describe, before, after } from 'node:test';
import assert from 'node:assert/strict';
import { spawn, execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { blake3 } from '@noble/hashes/blake3.js';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const BASE = 'http://127.0.0.1:5000';
const PROJECT = 'tekne-d1596';

const manifest = JSON.parse(readFileSync(join(ROOT, 'static', 'cas.json'), 'utf8'));
const OBJECT_HASH = Object.keys(manifest.objects)[0];

let emulator;

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

/** Follow nothing: we want to observe redirects, not chase them. */
const raw = (path) => fetch(`${BASE}${path}`, { redirect: 'manual' });

before(
	async () => {
		try {
			execFileSync('sh', ['-c', 'command -v firebase'], { stdio: 'ignore' });
		} catch {
			throw new Error('`firebase` not on PATH — run these tests inside `nix develop`.');
		}

		emulator = spawn('firebase', ['emulators:start', '--only', 'hosting', '--project', PROJECT], {
			cwd: ROOT,
			stdio: 'ignore',
			detached: true
		});

		const deadline = Date.now() + 120_000;
		for (;;) {
			try {
				await fetch(`${BASE}/`, { redirect: 'manual' });
				return;
			} catch {
				if (Date.now() > deadline) throw new Error('hosting emulator did not start within 120s');
				await sleep(500);
			}
		}
	},
	{ timeout: 150_000 }
);

after(() => {
	// Detached, so kill the whole process group — the CLI spawns children.
	if (emulator?.pid) {
		try {
			process.kill(-emulator.pid, 'SIGTERM');
		} catch {
			/* already gone */
		}
	}
});

describe('pages are served as real HTML, not a hydrating 404 shell', () => {
	test('/ serves prerendered content', async () => {
		const res = await raw('/');
		assert.equal(res.status, 200);
		assert.match(await res.text(), /Krishnaswami/);
	});

	test('/blog returns 200 and contains actual post titles', async () => {
		const res = await raw('/blog');
		assert.equal(res.status, 200, '/blog must not 404 — see the file header');
		const body = await res.text();
		assert.match(body, /Paper Planes/);
		assert.match(body, /Ship of Thesis/);
	});

	test('a post is served prerendered, with its title in the HTML', async () => {
		const res = await raw('/blog/adventures-in-type-theory/paper-planes');
		assert.equal(res.status, 200);
		assert.match(await res.text(), /<title>[^<]*Paper Planes[^<]*<\/title>/);
	});

	test('feeds are served', async () => {
		for (const path of ['/rss.xml', '/sitemap.xml']) {
			const res = await raw(path);
			assert.equal(res.status, 200, `${path} should be 200`);
			assert.match(await res.text(), /tekne\.dev/);
		}
	});

	test('an unknown post still 404s', async () => {
		assert.equal((await raw('/blog/no-such-post')).status, 404);
	});
});

describe('URL compatibility', () => {
	test('/blog.html redirects to the clean URL', async () => {
		const res = await raw('/blog.html');
		assert.equal(res.status, 301);
		assert.equal(new URL(res.headers.get('location'), BASE).pathname, '/blog');
	});

	test('legacy bare slugs 301 to their canonical series path', async () => {
		const res = await raw('/blog/paper-planes');
		assert.equal(res.status, 301);
		assert.equal(
			new URL(res.headers.get('location'), BASE).pathname,
			'/blog/adventures-in-type-theory/paper-planes'
		);
	});

	test('a series directory lists its posts instead of 404ing', async () => {
		// This segment appears inside every canonical URL in the series, so
		// trimming a post URL to it must land somewhere real.
		const res = await raw('/blog/adventures-in-type-theory');
		assert.equal(res.status, 200);
		const body = await res.text();
		assert.match(body, /<title>[^<]*Adventures in Type Theory[^<]*<\/title>/);
		for (const slug of ['locally-nameless-stlc', 'coming-in-clutch', 'paper-planes']) {
			assert.match(
				body,
				new RegExp(`href="/blog/adventures-in-type-theory/${slug}"`),
				`topic page should link ${slug}`
			);
		}
		// Oldest first: part one must precede part five in document order.
		assert.ok(
			body.indexOf('locally-nameless-stlc') < body.indexOf('paper-planes'),
			'series should read oldest-first'
		);
	});

	test('a post links back to its series', async () => {
		const res = await raw('/blog/adventures-in-type-theory/paper-planes');
		assert.match(await res.text(), /href="\/blog\/adventures-in-type-theory"/);
	});

	test('"old" is not a topic — its posts live in the bare /blog namespace', async () => {
		assert.equal((await raw('/blog/old')).status, 404);
	});

	test('every post is reachable by uuid, so links survive reorganisation', async () => {
		const posts = JSON.parse(readFileSync(join(ROOT, 'build', 'api', 'posts'), 'utf8'));
		assert.ok(posts.length > 0, 'expected posts in the prerendered API');
		for (const post of posts) {
			const res = await raw(`/blog/${post.meta.uuid}`);
			assert.equal(res.status, 200, `uuid URL for "${post.meta.title}" should resolve`);
		}
	});
});

describe('content-addressed store', () => {
	test('a bare hash serves the bytes, untyped and immutable', async () => {
		const res = await raw(`/cas/${OBJECT_HASH}`);
		assert.equal(res.status, 200);
		assert.equal(res.headers.get('content-type'), 'application/octet-stream');
		assert.match(res.headers.get('cache-control'), /immutable/);
		assert.match(res.headers.get('cache-control'), /max-age=31536000/);
	});

	test('the bytes served actually hash to the name they were requested by', async () => {
		const bytes = new Uint8Array(await (await raw(`/cas/${OBJECT_HASH}`)).arrayBuffer());
		assert.equal(Buffer.from(blake3(bytes)).toString('hex'), OBJECT_HASH);
	});

	test('each name supplies the type and filename the object omits', async () => {
		for (const [name, n] of Object.entries(manifest.names)) {
			const res = await raw(name);
			assert.equal(res.status, 200, `${name} should serve directly, not redirect`);
			assert.equal(res.headers.get('content-type'), n.mediaType, `${name} content-type`);
			assert.match(
				res.headers.get('content-disposition') ?? '',
				new RegExp(`filename="${n.filename}"`),
				`${name} should name its download`
			);
		}
	});

	test('a name serves the same bytes as the object it points at', async () => {
		for (const [name, n] of Object.entries(manifest.names)) {
			const bytes = new Uint8Array(await (await raw(name)).arrayBuffer());
			assert.equal(Buffer.from(blake3(bytes)).toString('hex'), n.hash, `${name} bytes`);
		}
	});

	test('names are not cached as long as the immutable objects they point at', async () => {
		// A name is a mutable pointer. If it inherited `immutable`, republishing
		// under an existing name would never reach anyone who had visited it.
		for (const name of Object.keys(manifest.names)) {
			const cc = (await raw(name)).headers.get('cache-control') ?? '';
			assert.doesNotMatch(cc, /immutable/, `${name} must stay revisable`);
		}
	});

	test('the manifest itself is not served as immutable', async () => {
		const res = await raw('/cas.json');
		assert.equal(res.status, 200);
		assert.doesNotMatch(res.headers.get('cache-control') ?? '', /immutable/);
	});
});
