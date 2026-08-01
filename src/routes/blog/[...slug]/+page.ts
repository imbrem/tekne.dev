import { error } from '@sveltejs/kit';
import { buildPostLookup, buildTopics, isIndexedTopic } from '$lib/utils';
import type { PostLookupEntry, Topic } from '$lib/utils';

let lookupCache: Map<string, PostLookupEntry> | null = null;
let topicCache: Map<string, Topic> | null = null;

async function getLookup() {
	if (!lookupCache) {
		lookupCache = await buildPostLookup();
	}
	return lookupCache;
}

async function getTopics() {
	if (!topicCache) {
		topicCache = await buildTopics();
	}
	return topicCache;
}

export async function entries() {
	const [lookup, topics] = await Promise.all([getLookup(), getTopics()]);
	return [...lookup.keys(), ...topics.keys()].map((slug) => ({ slug }));
}

export async function load({ params }: { params: { slug: string } }) {
	// Posts win over topics: a post slug that collides with a directory name
	// should still resolve to the post, since that is the published URL.
	const lookup = await getLookup();
	const entry = lookup.get(params.slug);
	if (entry) {
		const mod = await entry.component();
		const { category } = entry.post;
		return {
			kind: 'post' as const,
			content: mod.default,
			meta: entry.post.meta,
			canonicalPath: entry.post.path,
			// Derived from the category directly rather than by loading the topic
			// index, which would pull every post's module into the client bundle.
			topicPath: isIndexedTopic(category) ? `/blog/${category}` : null
		};
	}

	const topics = await getTopics();
	const topic = topics.get(params.slug);
	if (topic) {
		return { kind: 'topic' as const, topic };
	}

	error(404, { message: 'Not found' });
}
