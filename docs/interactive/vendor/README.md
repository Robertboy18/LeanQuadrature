KaTeX 0.18.7 is vendored here so the reading guide can render LaTeX without
an external service. The JavaScript, auto-render extension, and WOFF2 fonts
are copied unchanged from the npm package's `dist` directory. The CSS keeps
only the WOFF2 source for each of the 20 font faces; duplicate WOFF and TTF
files are omitted. The package's MIT license is retained at `katex/LICENSE`.

Package: `katex@0.18.7`

Registry integrity:
`sha512-h+UCwkZ+4Jz8WQ7MLGfj7UVFrRCizGb912fwF4luGdYsC5paYG1vx+jy+KRcC/XkpjGva/P7nAWuxNnPzRvzHw==`

To refresh the assets, install an explicit version into local scratch space
and copy its renderer, extension, stylesheet, and WOFF2 fonts here. Remove the
stylesheet's WOFF and TTF fallbacks, keeping the CSS-relative `fonts/` path.
The page loads the renderer and extension before `app.js`. Static prose uses
`\(...\)` and `\[...\]`; interactive updates are typeset after their content changes.
