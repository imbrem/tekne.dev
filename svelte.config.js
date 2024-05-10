import adapter from '@sveltejs/adapter-static';
import { vitePreprocess } from '@sveltejs/vite-plugin-svelte';
import { mdsvex, escapeSvelte } from 'mdsvex';
import { bundledLanguages, getHighlighter } from 'shiki';
import remarkMath from 'remark-math';
import remarkFootnotes from 'remark-footnotes';
import rehypeKatexSvelte from 'rehype-katex-svelte';

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
					if (bundledLanguages[lang] == undefined) {
						lang = 'text'
					}
					const highlighter = await getHighlighter({
						themes: ['nord'],
						langs: [lang]
					})
					await highlighter.loadLanguage('javascript', 'typescript')
					const html = escapeSvelte(highlighter.codeToHtml(code, { lang, theme: 'nord' }))
					return `{@html \`${html}\` }`
				}
			},
			layout: {
				blog: 'src/routes/blog/post.svelte'
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
			fallback: '404.html',
		})
	}
};

export default config;
