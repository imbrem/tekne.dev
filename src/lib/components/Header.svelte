<script>
	import Home from '$lib/icons/Home.svelte';
	import Github from '$lib/icons/Github.svelte';
	import Gitlab from '$lib/icons/Gitlab.svelte';
	import Mail from '$lib/icons/Mail.svelte';
</script>

<header>
	<nav>
		<a aria-label="home" href="/">
			<Home />
		</a>

		<div>
			<ul>
				<li><a href="/blog">Blog</a></li>
				<li><a aria-label="github" href="https://github.com/imbrem"><Github /></a></li>
				<li><a aria-label="gitlab" href="https://gitlab.com/tekne"><Gitlab /></a></li>
				<li><a aria-label="email" href="mailto:jeg74@cl.cam.ac.uk"><Mail /></a></li>
			</ul>
		</div>
	</nav>
</header>

<style>
	nav {
		padding: 1rem;
		background: #333333;
		display: flex;
		flex-wrap: wrap;
		justify-content: space-between;
		border-radius: 10px;
	}

	ul {
		margin: 0;
		list-style-type: none;
		display: flex;
		gap: 1.5rem;
	}

	a {
		text-decoration: none;
		color: inherit;
	}

	a:hover {
		color: cyan;
	}
</style>
