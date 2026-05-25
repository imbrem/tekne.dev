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
	const seen = new Set<string>();
	const result: { slug: string }[] = [];
	for (const [key, entry] of lookup) {
		const id = entry.post.path;
		if (!seen.has(id)) {
			seen.add(id);
		}
		result.push({ slug: key });
	}
	return result;
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
