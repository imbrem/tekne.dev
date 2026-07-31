import { error } from '@sveltejs/kit';
import { buildPostLookup } from '$lib/utils';

let lookupCache: Map<string, import('$lib/utils').PostLookupEntry> | null = null;

async function getLookup() {
	if (!lookupCache) {
		lookupCache = await buildPostLookup();
	}
	return lookupCache;
}

export async function entries() {
	const lookup = await getLookup();
	return [...lookup.keys()].map((slug) => ({ slug }));
}

export async function load({ params }: { params: { slug: string } }) {
	const lookup = await getLookup();
	const entry = lookup.get(params.slug);
	if (!entry) {
		error(404, { message: 'Post not found' });
	}
	const mod = await entry.component();
	return {
		content: mod.default,
		meta: entry.post.meta,
		canonicalPath: entry.post.path
	};
}
