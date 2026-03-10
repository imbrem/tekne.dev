import * as config from '$lib/config';
import { fetchMarkdownPosts } from '$lib/utils';

export const prerender = true;

export async function GET() {
	const posts = await fetchMarkdownPosts();
	const sortedPosts = posts.sort(
		(a, b) => +new Date(b.meta.published) - +new Date(a.meta.published)
	);

	const staticPages = ['', 'blog'];

	const xml = `<?xml version="1.0" encoding="UTF-8" ?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
${staticPages
	.map(
		(page) => `<url>
<loc>${config.live_url}${page}</loc>
</url>`
	)
	.join('\n')}
${sortedPosts
	.map(
		(post) => `<url>
<loc>${config.live_url}${post.path.replace(/^\//, '')}</loc>
<lastmod>${post.meta.edited || post.meta.published}</lastmod>
</url>`
	)
	.join('\n')}
</urlset>`;

	return new Response(xml.trim(), {
		headers: { 'Content-Type': 'application/xml' }
	});
}
