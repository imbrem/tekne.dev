import { fetchMarkdownPosts } from "$lib/utils";
import { json } from '@sveltejs/kit';

export const GET = async () => {
    const allPosts = await fetchMarkdownPosts();

    const sortedPosts = allPosts.sort((a, b) => {
        return +new Date(b.meta.published) - +new Date(a.meta.published);
    });

    return json(sortedPosts);
}