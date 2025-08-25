const ROUTES_PREFIX = '/src/routes';
const EXTENSION = '.md';

export const fetchMarkdownPosts = async () => {
	const postFiles = import.meta.glob('/src/routes/blog/*.md');
	const iterablePostFiles = Object.entries(postFiles);
	return await Promise.all(
		iterablePostFiles.map(async ([path, resolver]) => {
			const { metadata } = (await resolver()) as any;
			const postPath = path.slice(ROUTES_PREFIX.length, -EXTENSION.length);
			return { meta: metadata, path: postPath };
		})
	);
};
