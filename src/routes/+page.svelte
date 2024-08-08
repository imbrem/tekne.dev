<script>
	import * as config from '$lib/config';
	import me from '$lib/assets/me.jpg';
</script>

<svelte:head>
	<title>{config.title}</title>
</svelte:head>

<h1>Jad Ghalayini</h1>
<hr />

<div id="profile">
	<div id="photo">
		<img src={me} alt="Nanosecond wise, hour foolish" style="width:100%; border-radius:5%" />
	</div>

	<div id="bio">
		<p>
			Hello, I'm Jad! I'm a PhD student at the University of Cambridge supervised by
			<a href="https://www.cl.cam.ac.uk/~nk480/">Neel Krishnaswami</a>, currently working on
			rigorous, categorical semantics for SSA form with complex side effects, such as weak
			memory. In my spare time, I enjoy learning languages, reading lore, and thinking of
			third items to put in lists. I also write far too much Lean.
		</p>

		My interests include:
		<ul id="interests">
			<li>Category Theory</li>
			<li>SSA</li>
			<li>Intermediate Representations</li>
			<li>Compiler Design</li>
			<li>Type Theory</li>
			<li>Formal Verification</li>
			<li>Concurrency</li>
			<li>Weak Memory</li>
		</ul>
	</div>
</div>

<h2>Publications</h2>

<ul>
	<li>
		<b>[<a href="https://dl.acm.org/doi/10.1145/3607837">ICFP'23</a>]</b>
		Explicit Refinement Types (J. Ghalayini,
		<a href="https://www.cl.cam.ac.uk/~nk480/">N. Krishnaswami</a>)
	</li>
</ul>

<style>
    #profile {
        display: flex;
    }

    @media only screen and (max-width: 700px) {
        #profile {
            flex-direction: column;
            align-items: center;
        }

        #photo {
            width: 300px;
            max-width: 80%;
            padding: 3em;
        }
    }

    @media only screen and (min-width: 700px) {
        #photo {
            min-width: 300px;
            max-width: 300px;
            padding: 2em;
        }
    }
</style>
