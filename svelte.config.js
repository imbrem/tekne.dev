import adapter from '@sveltejs/adapter-static';
import { vitePreprocess } from '@sveltejs/vite-plugin-svelte';
import { mdsvex, escapeSvelte } from 'mdsvex';
import { getSingletonHighlighter, bundledLanguages, bundledThemes } from 'shiki';
import remarkMath from 'remark-math';
import remarkFootnotes from 'remark-footnotes';
import rehypeKatexSvelte from 'rehype-katex-svelte';

const CODE_THEME = 'nord-tekne';

const nord = await bundledThemes.nord().then((m) => m.default);

// Nord, with two corrections. Appended rules win over the base ones.
const theme = {
	...nord,
	name: CODE_THEME,
	tokenColors: [
		...nord.tokenColors,
		// Nord's comment colour is #616E88 — 2.43:1 on its own #2E3440 background,
		// which fails WCAG AA. Lean here is doc-comment heavy, so this matters.
		{
			scope: ['comment', 'punctuation.definition.comment'],
			settings: { foreground: '#8FA1B3' }
		},
		// Nord styles invalid.illegal with a *background* and a normal foreground.
		// Shiki emits only `color`, so Lean's `sorry` came out identical to
		// ordinary code — the one token that must never be easy to miss.
		{ scope: 'invalid.illegal', settings: { foreground: '#EC8B92', fontStyle: 'bold' } }
	]
};

// vscode-lean4's `dashComment` rule includes `source.lean4.markdown`, which
// Shiki does not ship. An unresolvable include makes the TextMate engine drop
// the entire rule, so `-- line comments` were rendering completely unscoped.
// An empty stub is enough to make the include resolve.
const lean4Markdown = {
	name: 'lean4markdown',
	scopeName: 'source.lean4.markdown',
	patterns: []
};

// The same grammar has no tactic or operator patterns at all: VS Code colours
// those from LSP semantic tokens, which a static site cannot run. Left alone,
// roughly three quarters of the Lean on this site renders as undifferentiated
// grey. These two conservative, word-boundary passes cover the common cases.
const leanExtras = [
	{
		match:
			'(?<![\\w.])(?:simp|simpa|simp_all|rw|rwa|subst|omega|decide|norm_num|ring|linarith|aesop|tauto|constructor|rcases|obtain|rintro|intro|intros|apply|exact|refine|induction|cases|case|calc|conv|unfold|dsimp|exact\\?|assumption|contradiction|trivial|rfl|ext|funext|congr|generalize|specialize|revert|clear|have|show|suffices|change|first|repeat|try|all_goals|any_goals|focus|next|split|grind)(?![\\w.])',
		name: 'keyword.control.tactic.lean4'
	},
	{
		match: '[→↔∀∃λ¬∧∨≤≥≠∈∉⊆∘≫≪⟶⟹↦⊢⊣⊔⊓∅≡≅⁻¹×⊕⊗∑∏]|:=|=>|<\\||\\|>|←|↑|↓',
		name: 'keyword.operator.lean4'
	}
];

const leanBundled = await bundledLanguages.lean().then((m) => m.default);
const lean = (Array.isArray(leanBundled) ? leanBundled : [leanBundled]).map((g) =>
	g.scopeName === 'source.lean4' ? { ...g, patterns: [...leanExtras, ...g.patterns] } : g
);

const highlighter = await getSingletonHighlighter({
	themes: [theme],
	langs: [
		lean4Markdown,
		...lean,
		'rust',
		'c',
		'cpp',
		'python',
		'bash',
		'typescript',
		'javascript',
		'sql',
		'json',
		'toml',
		'text',
		'svelte',
		'asm'
	]
});

/** @type {import('@sveltejs/kit').Config} */
const config = {
	// Consult https://kit.svelte.dev/docs/integrations#preprocessors
	// for more information about preprocessors
	preprocess: [
		vitePreprocess(),
		mdsvex({
			extensions: ['.md'],
			highlight: {
				highlighter: async (code, lang = 'text') => {
					await highlighter.loadLanguage(lang);
					const html = escapeSvelte(highlighter.codeToHtml(code, { lang, theme: CODE_THEME }));
					return `{@html \`${html}\` }`;
				}
			},
			remarkPlugins: [remarkMath, remarkFootnotes],
			rehypePlugins: [rehypeKatexSvelte]
		})
	],

	extensions: ['.svelte', '.md'],

	kit: {
		// adapter-auto only supports some environments, see https://kit.svelte.dev/docs/adapter-auto for a list.
		// If your environment is not supported, or you settled on a specific environment, switch out the adapter.
		// See https://kit.svelte.dev/docs/adapters for more information about adapters.
		adapter: adapter({
			fallback: '404.html'
		})
	}
};

export default config;
