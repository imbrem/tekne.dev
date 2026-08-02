#!/usr/bin/env node
/**
 * Scaffold a new post with complete, correct frontmatter.
 *
 *   pnpm new-post <category> "<title>" [--slug s] [--description d] [--categories a,b]
 *
 * The point is that the file is right on arrival: at its final path, with a
 * `uuid` generated once and never changed, so a draft can sit on a branch for a
 * year and still merge cleanly.
 *
 * `series` is inherited from whatever the other posts in that directory declare,
 * which is what /blog/<category> titles itself from.
 */

import { randomUUID } from 'node:crypto';
import { readFileSync, writeFileSync, existsSync, mkdirSync, readdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');
const CONTENT = join(ROOT, 'src', 'content', 'blog');

const die = (msg) => {
	console.error(msg);
	process.exit(1);
};

const slugify = (s) =>
	s
		.normalize('NFKD')
		.replace(/[̀-ͯ]/g, '') // strip diacritics
		.replace(/['’]/g, '') // don't turn "ICFP'25" into "icfp-25"… keep it "icfp25"
		.toLowerCase()
		.replace(/[^a-z0-9]+/g, '-')
		.replace(/^-+|-+$/g, '');

// --- args ------------------------------------------------------------------

const argv = process.argv.slice(2);
const positional = [];
const flags = {};
for (let i = 0; i < argv.length; i++) {
	if (argv[i].startsWith('--')) flags[argv[i].slice(2)] = argv[++i];
	else positional.push(argv[i]);
}

const [category, title] = positional;
if (!category || !title) {
	die(
		'usage: pnpm new-post <category> "<title>" [--slug s] [--description d] [--categories a,b]\n' +
			'\ne.g.  pnpm new-post adventures-in-type-theory "Adventures in Type Theory 6 — ICFP\'25" --slug icfp-25'
	);
}

const slug = flags.slug ? slugify(flags.slug) : slugify(title);
if (!slug) die(`could not derive a slug from ${JSON.stringify(title)} — pass --slug`);

// --- collision checks ------------------------------------------------------

const allPosts = existsSync(CONTENT)
	? readdirSync(CONTENT, { recursive: true })
			.filter((p) => String(p).endsWith('.md'))
			.map((p) => join(CONTENT, String(p)))
	: [];

const frontmatterOf = (file) => {
	const m = readFileSync(file, 'utf8').match(/^---\n([\s\S]*?)\n---/);
	return m ? m[1] : '';
};

const dir = join(CONTENT, category);
const file = join(dir, `${slug}.md`);
if (existsSync(file)) die(`refusing to overwrite ${file}`);

const uuid = randomUUID();

// Slugs, unlike uuids, are chosen by hand and do collide. A bare slug is also a
// lookup key, so a clash across directories is real even when the canonical
// paths differ.
const clash = allPosts.find((f) => f.endsWith(`/${slug}.md`));
if (clash) die(`slug "${slug}" is already used by ${clash.replace(ROOT + '/', '')} — pass --slug`);

// --- inherit the series name from the directory ----------------------------

const siblings = existsSync(dir) ? readdirSync(dir).filter((f) => f.endsWith('.md')) : [];
const series = siblings
	.map((f) =>
		frontmatterOf(join(dir, f))
			.match(/^series:\s*(.+)$/m)?.[1]
			?.trim()
	)
	.find(Boolean);

// --- write -----------------------------------------------------------------

const today = new Date().toISOString().slice(0, 10);
const categories = flags.categories
	? `[${flags.categories
			.split(',')
			.map((c) => c.trim())
			.filter(Boolean)
			.join(', ')}]`
	: '[]';

const frontmatter = [
	'---',
	`title: ${title}`,
	`published: '${today}'`,
	`description: ${flags.description ?? ''}`,
	`categories: ${categories}`,
	...(series ? [`series: ${series}`] : []),
	`uuid: ${uuid}`,
	'---',
	''
].join('\n');

mkdirSync(dir, { recursive: true });
writeFileSync(file, frontmatter);

const url = category === 'old' ? `/blog/${slug}` : `/blog/${category}/${slug}`;

console.log(`created ${file.replace(ROOT + '/', '')}`);
console.log(`  url    ${url}`);
console.log(`  uuid   ${uuid}  (permanent — never change it once published)`);
if (series) console.log(`  series ${series}  (inherited from ${category}/)`);
console.log(`\nnext:`);
console.log(`  pnpm dev            # live preview at ${url}`);
if (!flags.description) {
	console.log(`  fill in description — RSS, the sitemap and the blog index all use it`);
}
console.log(`\nfor images, in the post body:`);
console.log(`  <script module>`);
console.log(`    import Img from "$lib/components/Img.svelte"`);
console.log(`    import pic from "$lib/assets/${slug}/pic.jpg?w=480;800;1200;1600;2400&enhanced"`);
console.log(`  </script>`);
console.log(`  <Img src={pic} alt="…" />`);
