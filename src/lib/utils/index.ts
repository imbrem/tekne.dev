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
