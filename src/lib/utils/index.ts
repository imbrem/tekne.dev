import type { Component } from 'svelte';

const CONTENT_PREFIX = '/src/content/blog/';
const EXTENSION = '.md';

export interface PostMeta {
	title: string;
	published: string;
	edited?: string;
	description?: string;
	categories?: string[];
	series?: string;
	uuid: string;
	aliases?: string[];
}

export interface Post {
	meta: PostMeta;
	path: string;
	slug: string;
	category: string;
}

export interface PostLookupEntry {
	post: Post;
	component: () => Promise<PostModule>;
}

/**
 * A directory under src/content/blog that appears in post URLs, listed at
 * /blog/<slug>. `old/` is excluded: its posts are served from the bare /blog/
 * namespace, so "old" is not a segment of any URL and has nothing to index.
 */
export interface Topic {
	slug: string;
	path: string;
	title: string;
	posts: Post[];
}

const UNINDEXED = new Set(['old', '']);

/** Whether a post's directory has a listing page at /blog/<category>. */
export const isIndexedTopic = (category: string) => !UNINDEXED.has(category);

const humanise = (slug: string) =>
	slug
		.split('-')
		.map((w) => w.charAt(0).toUpperCase() + w.slice(1))
		.join(' ');

export const buildTopics = async (): Promise<Map<string, Topic>> => {
	const posts = await fetchMarkdownPosts();
	const topics = new Map<string, Topic>();

	for (const post of posts) {
		if (UNINDEXED.has(post.category)) continue;
		const topic = topics.get(post.category) ?? {
			slug: post.category,
			path: `/blog/${post.category}`,
			// Prefer the series name the posts declare over the directory name.
			title: post.meta.series ?? humanise(post.category),
			posts: []
		};
		topic.posts.push(post);
		topics.set(post.category, topic);
	}

	// Oldest first: a series reads from part one, unlike the reverse-chronological
	// blog index.
	for (const topic of topics.values()) {
		topic.posts.sort((a, b) => +new Date(a.meta.published) - +new Date(b.meta.published));
	}

	return topics;
};

type PostModule = {
	default: Component;
	metadata: PostMeta;
};

export const fetchMarkdownPosts = async (): Promise<Post[]> => {
	const postFiles = import.meta.glob('/src/content/blog/**/*.md');
	const iterablePostFiles = Object.entries(postFiles);
	return await Promise.all(
		iterablePostFiles.map(async ([filePath, resolver]) => {
			const { metadata } = (await resolver()) as PostModule;
			const relativePath = filePath.slice(CONTENT_PREFIX.length, -EXTENSION.length);
			const parts = relativePath.split('/');
			const slug = parts[parts.length - 1];
			const category = parts.length > 1 ? parts.slice(0, -1).join('/') : '';
			const canonicalPath =
				category && category !== 'old' ? `/blog/${category}/${slug}` : `/blog/${slug}`;
			return {
				meta: metadata,
				path: canonicalPath,
				slug,
				category
			};
		})
	);
};

export const buildPostLookup = async (): Promise<Map<string, PostLookupEntry>> => {
	const postFiles = import.meta.glob('/src/content/blog/**/*.md');
	const lookup = new Map<string, PostLookupEntry>();

	for (const [filePath, resolver] of Object.entries(postFiles)) {
		const mod = (await resolver()) as PostModule;
		const meta = mod.metadata;
		const relativePath = filePath.slice(CONTENT_PREFIX.length, -EXTENSION.length);
		const parts = relativePath.split('/');
		const slug = parts[parts.length - 1];
		const category = parts.length > 1 ? parts.slice(0, -1).join('/') : '';
		const canonicalPath =
			category && category !== 'old' ? `/blog/${category}/${slug}` : `/blog/${slug}`;

		const post: Post = { meta, path: canonicalPath, slug, category };
		const entry: PostLookupEntry = {
			post,
			component: resolver as () => Promise<PostModule>
		};

		// Canonical path segments (without /blog/ prefix)
		const canonicalKey = category && category !== 'old' ? `${category}/${slug}` : slug;
		lookup.set(canonicalKey, entry);

		// Legacy slug (bare filename)
		if (category && category !== 'old') {
			lookup.set(slug, entry);
		}

		// UUID
		if (meta.uuid) {
			lookup.set(meta.uuid, entry);
		}

		// Aliases
		if (meta.aliases) {
			for (const alias of meta.aliases) {
				lookup.set(alias, entry);
			}
		}
	}

	return lookup;
};
