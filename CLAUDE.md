# CLAUDE.md

Personal website and blog for Jad Ghalayini (tekne.dev). SvelteKit 5 with
`adapter-static`, fully prerendered, deployed to Firebase Hosting.

## Commands

Package manager is **pnpm**. A Nix dev shell (`nix develop`, or `direnv allow`)
provides Node 24, pnpm and `firebase-tools`; the tests need `firebase` on PATH,
so run them inside it.

- `pnpm dev` / `pnpm build` / `pnpm preview` — dev server, static build, preview
- `pnpm test` — build, then CAS + hosting suites
- `pnpm test:cas` — CAS invariants only; no build or server
- `pnpm check` — svelte-check
- `pnpm lint` / `pnpm format` — Prettier + ESLint
- `pnpm cas -- <add|ls|verify|check|aliases>` — content-addressed store
- `firebase emulators:start --only hosting` — serve `build/` under real hosting rules
- `firebase deploy` — publish

pnpm's strict `node_modules` is deliberate — anything imported must be declared.
Dependency install scripts are blocked by default and an unapproved one is a hard
error; `pnpm-workspace.yaml` allows `sharp` (behind `@sveltejs/enhanced-img`).

## Layout

```
src/
├── app.html                  # shell: Google Analytics, KaTeX CDN
├── content/blog/             # posts, grouped by series
│   ├── adventures-in-type-theory/
│   └── old/                  # pre-series posts, served at /blog/<slug>
├── lib/
│   ├── assets/               # one subdirectory per post
│   ├── components/           # Header.svelte, Img.svelte (enhanced:img wrapper)
│   ├── config.ts, icons/, styles/style.css
│   └── utils/index.ts        # fetchMarkdownPosts(), buildPostLookup()
└── routes/
    ├── +page.svelte          # home: bio, publications
    ├── api/posts/            # JSON, sorted by publish date
    ├── rss.xml/, sitemap.xml/
    └── blog/[...slug]/       # catch-all, resolved via lookup table
scripts/cas.mjs               # content-addressed store tooling
static/cas/                   # store objects; manifest at static/cas.json
tests/                        # cas.test.mjs, hosting.test.mjs
```

## Blog

Posts are `.md` under `src/content/blog/`, **not** under `src/routes/`. MDsveX
preprocesses them into Svelte components. Frontmatter:

```yaml
---
title: Post Title
published: 'YYYY-MM-DD'
edited: 'YYYY-MM-DD' # optional
description: One-line summary for RSS, sitemap, blog index
categories: [type-theory, lean] # optional
series: Adventures in Type Theory # optional
uuid: <stable; never change once published>
aliases: [old-url-slug] # optional extra URLs resolving here
---
```

A post's directory sets its URL: `<series-dir>/<slug>.md` → `/blog/<series-dir>/<slug>`,
except `old/`, which serves at `/blog/<slug>` to preserve pre-restructure links.

Both consumers glob `/src/content/blog/**/*.md`:

- `fetchMarkdownPosts()` — flat list behind `/api/posts`, the index, RSS, sitemap.
- `buildPostLookup()` — the `[...slug]` resolution table. Each post registers under
  its canonical path, bare slug, `uuid`, **and** any `aliases`; `entries()`
  prerenders one page per key, so old links keep working.

Since URLs derive from filenames, **moving or renaming a published post breaks its
URL** — add the old slug to `aliases` in the same edit.

## Markdown

- **Code**: Shiki, Nord theme. Languages are preloaded in `svelte.config.js` — add
  new ones there or highlighting fails.
- **Math**: remark-math + rehype-katex-svelte (KaTeX CSS from CDN in `app.html`).
- **Footnotes**: remark-footnotes.
- **Images**: `@sveltejs/enhanced-img`. Import with `?enhanced` in a `<script module>`
  block, render via `$lib/components/Img.svelte`.
- **Mermaid is not available.** The dependency is gone and nothing ever initialised
  it. `svelte.config.js` still turns a `mermaid` fence into `<pre class="mermaid">`,
  which nothing renders, so it comes out as unstyled text.

## Styling

Dark theme (`#222222`), Fira Code, cyan links, 77rem max-width.

## Content-addressed store (`/cas/`)

`static/cas/<hash>` (BLAKE3), served at `/cas/<hash>`: bytes only — no extension,
no media type, no filename. Objects are committed, so the repo _is_ the store and
nothing can drift from it. Media type, download filename and title belong to a
**name** pointing at the object.

`static/cas.json` (served at `/cas.json`) holds immutable `objects`, mutable
`names`, and a `history` of retired name→hash bindings with dates.

Four things are deliberate and easy to break:

- **Objects are bare hashes** — type is not identity. `/cas/**` is served an
  explicit `application/octet-stream`, so `WebAssembly.instantiateStreaming()` will
  reject a `/cas/` URL; fetch to an `ArrayBuffer`, or give the module a name.
- **The manifest sits outside `/cas/`**, which is served `immutable`.
- **Names are rewrites plus a per-name header rule, never redirects.** Header rules
  match the _request_ path, so only a rule on the name can set `Content-Type` and
  `Content-Disposition`. A 302 inherits the object's (absent) type; a rewrite alone
  infers nothing from `.pdf`. The cost is dedup — an alias caches its own copy.
- **`firebase.json` is hand-maintained** (it also holds the blog's 301s). After any
  `add` that binds a name, update the rewrite _and_ its header rule, then run
  `pnpm cas -- check`.

## Hosting

Serves `build/` with 60s cache headers. **`cleanUrls: true` is load-bearing — do
not remove it.** The adapter emits `blog.html` and `blog/<slug>.html`; without
`cleanUrls` every extensionless URL misses and falls through to `404.html`, which
is an SPA shell that hydrates and renders the right page. The site then looks fine
in a browser while returning HTTP 404 and an empty document to every crawler. That
was live for about a year.

Consequences: `pnpm preview` goes through Vite and ignores `firebase.json`, so it
cannot catch this class of bug — use the emulator. And check the **status code**,
not the page: `curl -sI https://tekne.dev/blog` must return 200.

`firebase.json` also 301s legacy bare slugs to canonical series paths. Redirects
are evaluated _before_ static files, so they win over the identically-named pages
`buildPostLookup` also emits.

## Tests

- `tests/cas.test.mjs` — objects hash to their own names, carry no extension, names
  resolve and carry semantics, and history never references a dropped object (that
  would make a past URL unrecoverable).
- `tests/hosting.test.mjs` — drives the real hosting emulator and asserts status
  codes and served bytes, never whether a page renders. Covers the `cleanUrls`
  regression, uuid resolution, legacy redirects, and CAS headers and byte identity.

The emulator does **not** implement range requests (200 where production returns
206), so range behaviour — what makes range-querying a hosted SQLite database
viable — is only confirmable against the deployed site.

## Conventions

- Svelte 5 runes (`$props()`, `{@render children()}`)
- Tabs, single quotes, no trailing commas (`.prettierrc`)
- ESLint flat config (`eslint.config.js`)
