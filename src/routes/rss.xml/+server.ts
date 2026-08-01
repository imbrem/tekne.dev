import * as config from '$lib/config';
import { fetchMarkdownPosts } from '$lib/utils';

export const prerender = true;

export async function GET() {
	const posts = await fetchMarkdownPosts();
	const sortedPosts = posts.sort(
		(a, b) => +new Date(b.meta.published) - +new Date(a.meta.published)
	);

	const absolute = (path: string) => `${config.live_url}${path.replace(/^\//, '')}`;

	/**
	 * A reader treats <guid> as the item's identity. Using the URL means any
	 * reorganisation — a post moving into a series directory, say — changes every
	 * guid and every subscriber sees the whole back catalogue reappear as unread.
	 * The `uuid` frontmatter is stable by contract precisely so it can be used
	 * here, as an opaque URN rather than a permalink. Posts predating the field
	 * fall back to the URL, which is no worse than before.
	 */
	const guid = (post: (typeof sortedPosts)[number]) =>
		post.meta.uuid
			? `<guid isPermaLink="false">urn:uuid:${escape(post.meta.uuid)}</guid>`
			: `<guid isPermaLink="true">${absolute(post.path)}</guid>`;

	// Derived from the newest post rather than the clock: the feed is prerendered,
	// so a build-time `new Date()` would churn on every deploy and make the output
	// non-reproducible.
	const lastBuildDate = sortedPosts.length
		? new Date(sortedPosts[0].meta.edited ?? sortedPosts[0].meta.published).toUTCString()
		: undefined;

	const xml = `<?xml version="1.0" encoding="UTF-8" ?>
<rss version="2.0" xmlns:atom="http://www.w3.org/2005/Atom">
<channel>
<title>${escape(config.title)}</title>
<link>${config.live_url}</link>
<description>Blog by ${escape(config.author)}</description>
<language>en</language>
<atom:link href="${config.live_url}rss.xml" rel="self" type="application/rss+xml" />${
		lastBuildDate ? `\n<lastBuildDate>${lastBuildDate}</lastBuildDate>` : ''
	}
${sortedPosts
	.map(
		(post) => `<item>
<title>${escape(post.meta.title)}</title>
<link>${absolute(post.path)}</link>
${guid(post)}
<pubDate>${new Date(post.meta.published).toUTCString()}</pubDate>${post.meta.description ? `\n<description>${escape(post.meta.description)}</description>` : ''}
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
