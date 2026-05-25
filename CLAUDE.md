# CLAUDE.md

## Project Overview

Personal website and blog for Jad Ghalayini (tekne.dev). Static site built with SvelteKit, deployed to Firebase Hosting.

## Commands

- `npm run dev` — Start dev server
- `npm run build` — Build static site to `build/`
- `npm run preview` — Preview production build
- `npm run check` — Type-check with svelte-check
- `npm run lint` — Prettier + ESLint
- `npm run format` — Auto-format with Prettier
- `firebase deploy` — Deploy to Firebase Hosting

## Architecture

### Framework

SvelteKit 5 with `@sveltejs/adapter-static` for static site generation. All pages are prerendered.

### Key Directories

```
src/
├── app.html                     # HTML shell (Google Analytics, KaTeX CDN)
├── lib/
│   ├── assets/                  # Images organized by blog post
│   ├── components/Header.svelte # Navigation header
│   ├── config.ts                # Site config (title, author, URLs)
│   ├── icons/                   # SVG icon components (Home, Github, Gitlab, Mail)
│   ├── styles/style.css         # Global styles (dark theme, Fira Code font)
│   └── utils/index.ts           # fetchMarkdownPosts() utility
├── routes/
│   ├── +layout.svelte           # Root layout
│   ├── +layout.ts               # prerender = true
│   ├── +page.svelte             # Home page (bio, publications)
│   ├── api/posts/+server.ts     # JSON API returning sorted blog posts
│   └── blog/
│       ├── +page.svelte         # Blog index
│       ├── +page.ts             # Fetches from /api/posts
│       ├── [slug]/              # Dynamic blog post route
│       └── *.md                 # Blog post markdown files
static/
├── favicon.png
└── ert.pdf
```

### Blog System

Blog posts are `.md` files in `src/routes/blog/`. They use MDsveX (markdown preprocessed as Svelte components) with frontmatter metadata:

```yaml
---
title: Post Title
published: YYYY-MM-DD
edited: YYYY-MM-DD # optional
---
```

Posts are auto-discovered via `import.meta.glob('/src/routes/blog/*.md')` in `fetchMarkdownPosts()`. The `/api/posts` endpoint returns them sorted by publish date.

### Markdown Features

- **Code highlighting**: Shiki with Nord theme (Lean language preloaded)
- **Math**: LaTeX via remark-math + rehype-katex-svelte
- **Diagrams**: Mermaid (rendered as `<pre class="mermaid">`)
- **Footnotes**: remark-footnotes
- **Images**: `@sveltejs/enhanced-img` for optimization

### Styling

- Dark theme (#222222 background)
- Fira Code monospace font
- Cyan accent color for links/hover
- Responsive layout with 77rem max-width

### Deployment

Firebase Hosting serving from `build/` directory with 60-second cache headers.

## Conventions

- Svelte 5 runes syntax (`$props()`, `{@render children()}`, etc.)
- Tabs for indentation, single quotes, no trailing commas (see .prettierrc)
- ESLint flat config (eslint.config.js)
