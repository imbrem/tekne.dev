import * as config from '$lib/config';
import { fetchMarkdownPosts } from '$lib/utils';

export const prerender = true;

export async function GET() {
	const posts = await fetchMarkdownPosts();
	const sortedPosts = posts.sort(
		(a, b) => +new Date(b.meta.published) - +new Date(a.meta.published)
	);

	const xml = `<?xml version="1.0" encoding="UTF-8" ?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
<channel>
<title>${escape(config.title)}</title>
<link>${config.live_url}</link>
<description>Blog by ${escape(config.author)}</description>
<atom:link href="${config.live_url}rss.xml" rel="self" type="application/rss+xml" />
${sortedPosts
	.map(
		(post) => `<item>
<title>${escape(post.meta.title)}</title>
<link>${config.live_url}${post.path.replace(/^\//, '')}</link>
<guid isPermaLink="true">${config.live_url}${post.path.replace(/^\//, '')}</guid>
<pubDate>${new Date(post.meta.published).toUTCString()}</pubDate>
</item>`
	)
	.join('\n')}
</channel>
</rss>`;

	return new Response(xml.trim(), {
		headers: { 'Content-Type': 'application/xml' }
	});
}

function escape(str: string): string {
	return str
		.replace(/&/g, '&amp;')
		.replace(/</g, '&lt;')
		.replace(/>/g, '&gt;')
		.replace(/"/g, '&quot;');
}
