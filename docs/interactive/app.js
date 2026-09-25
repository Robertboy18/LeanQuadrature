"use strict";

(() => {
  const $ = (selector) => document.querySelector(selector);
  const $$ = (selector) => [...document.querySelectorAll(selector)];
  const state = { nodes: 2, fn: "paper", convention: "count", proof: 0, route: "lean", loop: 0 };
  const ordinal = { 2: "second", 4: "fourth", 6: "sixth", 8: "eighth" };
  const names = { 1: "One", 2: "Two", 3: "Three", 4: "Four" };
  const mathOptions = { throwOnError: true, strict: "error", trust: false, output: "htmlAndMathml" };

  function typeset(element = document.body) {
    renderMathInElement(element, {
      ...mathOptions,
      delimiters: [
        { left: "\\[", right: "\\]", display: true },
        { left: "\\(", right: "\\)", display: false }
      ]
    });
  }

  function setMath(selector, expression) {
    const element = $(selector);
    element.dataset.tex = expression;
    katex.render(expression, element, mathOptions);
  }

  const functions = {
    paper: {
      label: "f(x) = ½(1 − x) cos x",
      tex: String.raw`f(x)=\tfrac12(1-x)\cos x`,
      value: (x) => 0.5 * (1 - x) * Math.cos(x),
      integral: Math.sin(1),
      integralLabel: String.raw`\sin 1`,
      maxY: 0.75
    },
    quartic: {
      label: "f(x) = x⁴",
      tex: String.raw`f(x)=x^4`,
      value: (x) => x ** 4,
      integral: 2 / 5,
      integralLabel: String.raw`\frac25`,
      maxY: 1.1
    },
    cubic: {
      label: "f(x) = x³ + x² + 1",
      tex: String.raw`f(x)=x^3+x^2+1`,
      value: (x) => x ** 3 + x ** 2 + 1,
      integral: 8 / 3,
      integralLabel: String.raw`\frac83`,
      maxY: 3.3
    }
  };

  function rule(n) {
    if (n === 1) return { nodes: [0], weights: [2] };
    if (n === 2) return { nodes: [-1 / Math.sqrt(3), 1 / Math.sqrt(3)], weights: [1, 1] };
    if (n === 3) return { nodes: [-Math.sqrt(3 / 5), 0, Math.sqrt(3 / 5)], weights: [5 / 9, 8 / 9, 5 / 9] };
    const outer = Math.sqrt((3 + 2 * Math.sqrt(6 / 5)) / 7);
    const inner = Math.sqrt((3 - 2 * Math.sqrt(6 / 5)) / 7);
    const small = (18 - Math.sqrt(30)) / 36;
    const large = (18 + Math.sqrt(30)) / 36;
    return { nodes: [-outer, -inner, inner, outer], weights: [small, large, large, small] };
  }

  function computation(n, key) {
    const r = rule(n);
    const fn = functions[key];
    const samples = r.nodes.map((x, i) => ({ x, weight: r.weights[i], value: fn.value(x), contribution: r.weights[i] * fn.value(x) }));
    const displayedSum = samples.reduce((sum, s) => sum + s.contribution, 0);
    const exact = (key === "quartic" && n >= 3) || (key === "cubic" && n >= 2);
    // Exactness is a mathematical property of these polynomials, not a tolerance test.
    const sum = exact ? fn.integral : displayedSum;
    return { samples, sum, error: exact ? 0 : Math.abs(fn.integral - sum), exact };
  }

  function decimal(value, digits = 15) {
    if (value === 0) return "0";
    return value.toPrecision(digits).replace(/(\.\d*?[1-9])0+(?=e|$)/, "$1").replace(/\.0+(?=e|$)/, "");
  }

  function errorDecimal(value) {
    if (value === 0) return "0 — exact";
    if (value < 0.000001) return value.toExponential(7);
    return value.toFixed(12).replace(/0+$/, "").replace(/\.$/, "");
  }

  function selectButtons(attribute, value) {
    $$(`[data-${attribute}]`).forEach((button) => {
      button.setAttribute("aria-pressed", String(button.dataset[attribute] === String(value)));
    });
  }

  function drawPlot(fn, samples) {
    const svg = $("#quadrature-plot");
    const left = 43, right = 690, top = 24, bottom = 263;
    const sx = (x) => left + (x + 1) / 2 * (right - left);
    const sy = (y) => bottom - y / fn.maxY * (bottom - top);
    let path = "";
    for (let i = 0; i <= 240; i++) {
      const x = -1 + 2 * i / 240;
      path += `${i === 0 ? "M" : "L"}${sx(x).toFixed(2)},${sy(fn.value(x)).toFixed(2)} `;
    }
    const parts = [
      `<title id="plot-title">${state.nodes}-point Gaussian quadrature for ${fn.label}</title>`,
      `<desc id="plot-desc">Function curve and ${state.nodes} sample nodes on minus one to one. Each node is labelled. The table below gives its weight and contribution.</desc>`,
      `<path class="plot-fill" d="${path}L${right},${bottom}L${left},${bottom}Z"/>`
    ];
    for (let i = 1; i <= 3; i++) {
      const y = fn.maxY * i / 4;
      parts.push(`<line class="plot-grid" x1="${left}" x2="${right}" y1="${sy(y)}" y2="${sy(y)}"/>`);
      parts.push(`<text class="plot-tick" x="${left - 10}" y="${sy(y) + 4}" text-anchor="end">${y.toFixed(2).replace(/0$/, "")}</text>`);
    }
    parts.push(`<line class="plot-axis" x1="${left}" x2="${right}" y1="${bottom}" y2="${bottom}"/>`);
    [-1, -0.5, 0, 0.5, 1].forEach((x) => {
      parts.push(`<line class="plot-axis" x1="${sx(x)}" x2="${sx(x)}" y1="${bottom}" y2="${bottom + 5}"/>`);
      parts.push(`<text class="plot-tick" x="${sx(x)}" y="${bottom + 24}" text-anchor="middle">${x}</text>`);
    });
    parts.push(`<text class="plot-tick" x="${right}" y="${bottom + 47}" text-anchor="end">x</text>`);
    parts.push(`<path class="plot-path" d="${path}"/>`);
    samples.forEach((s, i) => {
      const x = sx(s.x), y = sy(s.value);
      parts.push(`<g class="sample" tabindex="0" role="img" aria-label="Node ${i + 1}: x ${decimal(s.x, 6)}, weight ${decimal(s.weight, 6)}, function value ${decimal(s.value, 6)}"><title>Node ${i + 1}: x = ${decimal(s.x, 8)}, weight = ${decimal(s.weight, 8)}</title><line class="sample-stem" x1="${x}" x2="${x}" y1="${y}" y2="${bottom}"/><circle class="sample-point" cx="${x}" cy="${y}" r="5.8"/><text class="sample-label" x="${x}" y="${Math.max(14, y - 15)}" text-anchor="middle">x${["₁", "₂", "₃", "₄"][i]}</text></g>`);
    });
    svg.innerHTML = parts.join("");
  }

  function updateExplorer() {
    const n = state.nodes;
    const fn = functions[state.fn];
    const result = computation(n, state.fn);
    $("#node-count").value = n;
    $("#node-output").textContent = n;
    setMath("#function-label", fn.tex);
    $("#integral-value").textContent = decimal(fn.integral);
    setMath("#integral-expression", fn.integralLabel);
    $("#quadrature-value").textContent = decimal(result.sum);
    $("#error-value").textContent = errorDecimal(result.error);
    $("#error-explanation").textContent = result.exact ? "The ideal rule is exactly correct for this polynomial." : "Already present in exact real arithmetic.";
    let expression = String.raw`\sum_i w_i f(x_i)`;
    if (state.fn === "paper" && n === 1) expression = "2f(0) = 1";
    if (state.fn === "paper" && n === 2) expression = String.raw`\cos(1/\sqrt3)`;
    if (state.fn === "quartic") expression = n === 1 ? "0" : n === 2 ? String.raw`\frac29` : String.raw`\frac25\text{, exactly}`;
    if (state.fn === "cubic") expression = n === 1 ? "2" : String.raw`\frac83\text{, exactly}`;
    setMath("#quadrature-expression", expression);
    const exactness = String.raw`${names[n]} Gaussian ${n === 1 ? "node integrates" : "nodes integrate"} every polynomial through degree \(${2 * n - 1}\) exactly.`;
    $("#exactness-note").textContent = exactness + (state.fn === "paper" ? " This cosine-based function is not a polynomial." : state.fn === "quartic" && n === 2 ? String.raw` The quartic \(x^4\) is just beyond that guarantee.` : result.exact ? " The selected polynomial is within that guarantee." : " The selected polynomial is beyond that guarantee.");
    typeset($("#exactness-note"));
    let insight;
    if (state.fn === "paper") {
      insight = ({
        1: String.raw`One node gives \(2f(0)=1\). Its distance from \(\sin1\) is about \(0.158529\), so the draft’s absolute bound of \(0.02\) is too small.`,
        2: String.raw`With two nodes, the weighted sum simplifies to \(\cos(1/\sqrt3)\). Its distance from \(\sin1\) is already larger than the draft’s claimed \(0.00223\).`,
        3: String.raw`Three nodes reduce the exact-rule error to about \(0.0000307891\). The independent certificate for the complete internal-polynomial program proves an upper bound of \(0.000031\).`,
        4: String.raw`Four nodes reduce the exact-rule error to about \(0.00000014046\). The complete internal-polynomial program has a separately proved upper bound of \(0.00000015\).`
      })[n];
    } else if (state.fn === "quartic") {
      insight = n === 1 ? String.raw`One node samples \(x^4\) only at zero, giving \(Q=0\). The integral is \(2/5\).` : n === 2 ? String.raw`The exact error is \(2/5-2/9=8/45\). Yet the sixth derivative of \(x^4\) is zero. This refutes the draft’s sixth-derivative remainder for its two-node rule.` : `${names[n]} nodes integrate this quartic exactly. The two-node counterexample does not contradict a correctly indexed theorem about three or more nodes.`;
    } else {
      insight = n === 1 ? String.raw`One node is only guaranteed to integrate degree 1. This cubic gives \(Q=2\), while its integral is \(8/3\).` : "The rule integrates this cubic exactly. Tiny residuals a numerical implementation might produce are separate from this exact-real statement.";
    }
    $("#explorer-insight").textContent = insight;
    typeset($("#explorer-insight"));
    $("#samples-body").innerHTML = result.samples.map((s, i) => `<tr><th scope="row">${i + 1}</th><td>${decimal(s.x, 9)}</td><td>${decimal(s.weight, 9)}</td><td>${decimal(s.value, 9)}</td><td>${decimal(s.contribution, 9)}</td></tr>`).join("");
    selectButtons("function", state.fn);
    drawPlot(fn, result.samples);
    updateConvention();
  }

  function updateConvention() {
    const N = state.nodes;
    const index = state.convention === "index";
    const n = index ? N - 1 : N;
    $("#physical-nodes").textContent = `${N} ${N === 1 ? "node" : "nodes"}`;
    setMath("#convention-meaning", index ? String.raw`N=n+1=${N},\quad n=${n}` : `n=N=${N}`);
    setMath("#convention-formula", index ? String.raw`2n+2=2\times ${n}+2=${2 * N}` : String.raw`2n=2\times ${n}=${2 * N}`);
    $("#convention-result").textContent = `The ${ordinal[2 * N]} derivative.`;
    $("#convention-nodes").innerHTML = Array.from({ length: N }, (_, i) => String.raw`<span class="index-node"><span class="dot" aria-hidden="true"></span><span>\(x_{${index ? i : i + 1}}\)</span></span>`).join("");
    typeset($("#convention-nodes"));
    $("#convention-explanation").textContent = index
      ? String.raw`Indices 0 through ${n} give ${N} ${N === 1 ? "node" : "nodes"}. Here \(n=${n}\), so \(2n+2=${2 * N}\). The physical rule has not changed.`
      : String.raw`When \(n\) counts the nodes, a ${N}-node rule has \(n=${n}\). The remainder uses derivative order \(2n=${2 * N}\).`;
    typeset($("#convention-explanation"));
    selectButtons("convention", state.convention);
  }

  const proofs = [
    {
      eyebrow: "Real analysis", title: "How close is the exact sum to the integral?",
      body: "Prove that replacing the integral by a finite sum introduces at most the stated error. This error exists even when every number and arithmetic operation is exact.",
      example: String.raw`For two nodes in the paper’s example, the exact sum is \(\cos(1/\sqrt3)\), while the integral is \(\sin 1\). Their difference is about \(0.0035591571\). This is a claim about the numerical method before any C program enters the picture.`,
      formula: String.raw`\lvert I-Q\rvert\leq\varepsilon_{\mathrm{method}}`,
      scope: "General finite-interval theory is proved in Lean. Rocq has reusable analysis for orders 1–4 and independent bounds for all ten fixed polynomial applications.",
      href: "https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean", link: "Corrected remainder theorem"
    },
    {
      eyebrow: "Numerical implementation", title: "How much error comes from representing and evaluating the sum?",
      body: "Account for stored approximations to the nodes and weights, the implemented function’s error, and each rounded multiplication and addition. Bounds on intermediate magnitudes establish that the products and sums stay finite.",
      example: String.raw`For the certified two-point FloatLib example, the error relative to exact quadrature is at most \(2\times10^{-14}\). This proves accuracy of the modeled arithmetic. A separate program proof establishes that the C loop executes that model.`,
      formula: String.raw`\lvert v-Q\rvert\leq\varepsilon_{\mathrm{numeric}}`,
      scope: "Lean has general-integrand certificates for all ten original stored tables, under callback, derivative, and range hypotheses. Rocq has separate general numerical theorems for orders 1–4 and fixed-application certificates for all ten. Model correspondence remains a separate obligation.",
      href: "../../Quadrature/Clight/RuleAccuracy.lean", link: "General Lean bound for all ten tables"
    },
    {
      eyebrow: "Program correctness", title: "Does the C loop execute the functional model?",
      body: "Show that the arrays hold the specified values, that each access is valid, and that each iteration updates the accumulator exactly as the functional model specifies. Also prove termination and the return value, under explicit assumptions about the callback.",
      example: String.raw`For orders 1–10, Lean proves that every permitted evaluation order of the initialized C integrator terminates with \(F_L\). The selected library includes the original functions, their tables, and a verified C polynomial replacing cosine. Table and callback contracts are discharged, and every result has its certified integral-error bound.`,
      formula: String.raw`\operatorname{return}(C)=F_L`,
      scope: "Lean also proves preservation through normalization for the six selected functions and relates the C library’s returned values to the assembly applications’ result annotations. Both frontend outputs initialize and resolve the actual calls. General parser and compiler correctness, correspondence with Rocq’s definitions, native linking, and printing remain open.",
      href: "../../Quadrature/CSource/Library/Preservation.lean", link: "Initialized C-to-Clight preservation"
    },
    {
      eyebrow: "Compiler correctness", title: "Does compilation preserve that behavior?",
      body: "Use the compiler’s correctness theorems to carry established C behavior into assembly semantics. Compiler correctness does not prove a new integral-error bound: it preserves the behavior to which the numerical theorem already applies.",
      example: "In Rocq, all ten stored orders of the internal-polynomial application have checked compilation success, termination, unique annotated output, and integral-error bounds. Lean directly proves total correctness of the assembly applications and relates their reported values to the C library’s returns. This does not prove that compiling the original C text produces these assembly trees. Representation correspondence, instruction expansion, linking, and printing remain open.",
      formula: String.raw`\mathrm{behavior}(C)\ \leadsto\ \mathrm{behavior}(A)`,
      scope: "Concrete certificates use an explicit compiler configuration. Their endpoint is formal assembly semantics; assembly/linking and verified runtime output remain outside the certificate.",
      href: "../../compcert/certification/CertifiedStoredPolynomial.v", link: "Ten concrete assembly certificates"
    }
  ];

  function updateProof() {
    const p = proofs[state.proof];
    $("#proof-content").innerHTML = String.raw`<div><p class="eyebrow">${p.eyebrow}</p><h3>${p.title}</h3><p>${p.body}</p><p>${p.example}</p></div><aside class="proof-aside"><p class="small-label">What the connection establishes</p><div class="proof-formula">\(${p.formula}\)</div><p class="proof-scope">${p.scope}</p><a href="${p.href}">${p.link} ↗</a></aside>`;
    typeset($("#proof-content"));
    selectButtons("proof", state.proof);
  }

  function updateRoute() {
    if (state.route === "lean") {
      $("#route-content").innerHTML = String.raw`
        <div class="route-status"><span class="status-pill closed">Ten Lean applications with certified observations</span><p>Initialized authored callers, accurate result annotations, and exit status zero.</p></div>
        <div class="route-diagram">
          <div class="route-node"><p class="eyebrow">Lean · numerical accuracy</p><h3>FloatLib result and error</h3><div class="route-equation">\(\lvert v_L-I\rvert\leq\varepsilon\)</div><p>All ten stored orders have certified binary64 results and integral-error bounds for the fixed polynomial application.</p></div>
          <div class="route-node"><p class="eyebrow">Lean · application execution proved</p><h3>Loop, caller, and observation</h3><div class="route-equation">\(v_{\mathrm{observed}}=F_L\)</div><p>The initialized polynomial application discharges the loop’s conditions. Its authored caller records the exact returned value and exits with status zero. Every final observation has the certified integral bound for that order.</p></div>
          <div class="route-node"><p class="eyebrow">Lean · formal assembly proved</p><h3>Instructions, calls, and returns</h3><div class="route-equation">\(\lvert v_{\mathrm{asm}}-I\rvert\leq\varepsilon\)</div><p>All ten imported assembly programs have total-correctness proofs. Every execution reports exactly the value returned by the initialized C library and exits zero. General compiler correctness, representation correspondence, native linking, and printing remain open.</p></div>
        </div>
        <p class="route-footnote"><strong>The C return and assembly result are connected by a Lean theorem.</strong> Every permitted C evaluation order returns the certified FloatLib value; the corresponding assembly application reports that same value and exits zero. See <a href="#source-total-correctness">why every order is covered</a>, <a href="#source-normalization">preservation through Clight normalization</a>, and <a href="#source-assembly-observations">the return-to-annotation theorem</a>. The direct C-to-assembly result needs no external-call determinism premise; the companion connection to the authored Clight application retains its existing premise. This proves agreement for these programs, without a general compiler theorem or a proof that compiling the original C text produces their assembly trees. The endpoint is a formal annotation; printing and linking need further work. <a href="../../evidence/lean-quality.json">Lean build and audit ↗</a></p>`;
    } else if (state.route === "bridge") {
      $("#route-content").innerHTML = String.raw`
        <div class="route-status"><span class="status-pill">General connection open</span><p>The numerical and C proofs refer to different floating-point models.</p></div>
        <div class="route-diagram">
          <div class="route-node"><p class="eyebrow">Lean · proved</p><h3>FloatLib accuracy</h3><div class="route-equation">\(\lvert v_L-I\rvert\leq\varepsilon\)</div><p>The value produced by FloatLib’s computation is within the required distance of the integral.</p></div>
          <div class="route-node open"><p class="eyebrow">Connection · open</p><h3>Relate the two results</h3><div class="route-equation">\(v_R=v_L\)</div><p>Establish the relationship between the actual computations on the intended inputs, and connect the proofs in a checked construction. The proposed bitwise correspondence is stronger than this displayed equality.</p></div>
          <div class="route-node rocq"><p class="eyebrow">Rocq · proved under contracts</p><h3>C execution</h3><div class="route-equation">\(\operatorname{return}(C)=F_R\)</div><p>The loop returns the float defined by CompCert’s Flocq-based model. Its decoded real value is \(v_R\). The C-to-model proof on this side is already present.</p></div>
        </div>
        <p class="route-footnote">The Lean result has not been imported into the Rocq proof. The separate direct Lean route proves execution for all ten stored orders with our polynomial callback, and integral bounds for all ten. It does not establish this general correspondence.</p>`;
    } else {
      $("#route-content").innerHTML = String.raw`
        <div class="route-status"><span class="status-pill closed">Ten applications certified</span><p>This route proves numerical accuracy independently in Rocq.</p></div>
        <div class="route-diagram">
          <div class="route-node rocq"><p class="eyebrow">Rocq · numerical accuracy</p><h3>Bound the Rocq result directly</h3><div class="route-equation">\(\lvert v_R-I\rvert\leq\varepsilon\)</div><p>The integral identity, concrete result values, and error bounds are proved here independently. The numerical theorem already concerns \(F_R\).</p></div>
          <div class="route-node rocq"><p class="eyebrow">Rocq · application execution</p><h3>Loop, caller, and observation</h3><div class="route-equation">\(v_{\mathrm{observed}}=F_R\)</div><p>The internal polynomial and imported loop return the proved float. The authored caller records that exact value in an annotation and exits with status zero.</p></div>
          <div class="route-node rocq"><p class="eyebrow">Rocq · configured CompCert</p><h3>Assembly behavior</h3><div class="route-equation">\(\lvert v_{\mathrm{asm}}-I\rvert\leq\varepsilon\)</div><p>Successful compilation and unique terminating behavior transfer the result to formal assembly execution for each of the ten applications.</p></div>
        </div>
        <p class="route-footnote">These are certificates in CompCert’s assembly semantics. They do not verify a linked native executable, the platform cosine, or printf output.</p>`;
    }
    typeset($("#route-content"));
    selectButtons("route", state.route);
  }

  const loopSteps = [
    {
      title: "Both descriptions start from the same zero.",
      model: String.raw`a_0=+0`,
      program: String.raw`i=0,\qquad \mathtt{sum}=+0`,
      explanation: "No samples have been processed. The initialized C variable must hold the model’s positive zero. The table contents and callback contract are also part of the starting assumptions."
    },
    {
      title: "The first C iteration must match the first model step.",
      model: String.raw`a_1=\operatorname{add}(a_0,p_0)`,
      program: String.raw`i=1,\qquad \mathtt{sum}=a_1`,
      explanation: String.raw`C reads the first node and weight, calls the callback, multiplies, and adds to the accumulator. The proof relates these actions to \(p_0=\operatorname{mul}(\widehat w_0,\widehat f(\widehat x_0))\) and then to \(a_1\).`
    },
    {
      title: "After two matching steps, the return value is the model’s result.",
      model: String.raw`a_2=\operatorname{add}(a_1,p_1)=F`,
      program: String.raw`i=2,\qquad \mathtt{return}\ \mathtt{sum}=a_2`,
      explanation: String.raw`The second iteration processes the second sample. The loop condition is now false, and C returns the accumulator. Because the invariant still holds, that value is \(a_2=F\). A loop stopping one iteration earlier would return \(a_1\), which this specification does not permit in general.`
    }
  ];

  function updateLoop() {
    const step = loopSteps[state.loop];
    $("#loop-content").innerHTML = String.raw`
      <h3>${step.title}</h3>
      <div class="loop-pair">
        <div><span class="small-label">Functional model</span><div class="equation-block">\[${step.model}\]</div></div>
        <div><span class="small-label">C state at the loop test or return</span><div class="equation-block">\[${step.program}\]</div></div>
      </div>
      <p>${step.explanation}</p>`;
    typeset($("#loop-content"));
    selectButtons("loop", state.loop);
  }

  $("#node-count").addEventListener("input", (event) => {
    state.nodes = Number(event.target.value);
    updateExplorer();
  });
  $$("[data-function]").forEach((button) => button.addEventListener("click", () => {
    state.fn = button.dataset.function;
    updateExplorer();
  }));
  $$("[data-convention]").forEach((button) => button.addEventListener("click", () => {
    state.convention = button.dataset.convention;
    updateConvention();
  }));
  $$("[data-proof]").forEach((button) => button.addEventListener("click", () => {
    state.proof = Number(button.dataset.proof);
    updateProof();
  }));
  $$("[data-route]").forEach((button) => button.addEventListener("click", () => {
    state.route = button.dataset.route;
    updateRoute();
  }));
  $$("[data-loop]").forEach((button) => button.addEventListener("click", () => {
    state.loop = Number(button.dataset.loop);
    updateLoop();
  }));
  function loadExample(n, key) {
    state.nodes = n;
    state.fn = key;
    updateExplorer();
    $("#explore").scrollIntoView({ behavior: window.matchMedia("(prefers-reduced-motion: reduce)").matches ? "instant" : "smooth" });
    $("#node-count").focus({ preventScroll: true });
  }
  $("#load-counterexample").addEventListener("click", () => loadExample(2, "quartic"));
  $$("[data-load-example]").forEach((button) => button.addEventListener("click", () => loadExample(Number(button.dataset.loadExample), "paper")));

  const themeButton = $("#theme-button");
  const media = window.matchMedia("(prefers-color-scheme: dark)");
  let explicitTheme = null;
  try { explicitTheme = localStorage.getItem("quadrature-reading-theme"); } catch { /* Storage can be disabled for local files. */ }
  function setTheme(dark) {
    document.documentElement.dataset.theme = dark ? "dark" : "light";
    themeButton.setAttribute("aria-pressed", String(dark));
    themeButton.setAttribute("aria-label", dark ? "Use light reading theme" : "Use dark reading theme");
  }
  setTheme(explicitTheme ? explicitTheme === "dark" : media.matches);
  themeButton.addEventListener("click", () => {
    const dark = document.documentElement.dataset.theme !== "dark";
    setTheme(dark);
    explicitTheme = dark ? "dark" : "light";
    try { localStorage.setItem("quadrature-reading-theme", explicitTheme); } catch { /* Theme remains usable without storage. */ }
  });
  media.addEventListener("change", (event) => { if (!explicitTheme) setTheme(event.matches); });

  let scheduled = false;
  function updateScroll() {
    const distance = document.documentElement.scrollHeight - window.innerHeight;
    $("#reading-progress").style.width = `${distance > 0 ? Math.min(100, Math.max(0, window.scrollY / distance * 100)) : 0}%`;
    const nav = $$(".site-header nav a");
    let current = null;
    nav.forEach((link) => {
      const target = $(link.hash);
      if (target && target.getBoundingClientRect().top < 190) current = link;
    });
    nav.forEach((link) => {
      link.classList.toggle("current", link === current);
      if (link === current) link.setAttribute("aria-current", "location");
      else link.removeAttribute("aria-current");
    });
    scheduled = false;
  }
  window.addEventListener("scroll", () => {
    if (!scheduled) { scheduled = true; window.requestAnimationFrame(updateScroll); }
  }, { passive: true });
  window.addEventListener("resize", updateScroll);
  updateExplorer();
  updateProof();
  updateRoute();
  updateLoop();
  typeset();
  updateScroll();
})();
