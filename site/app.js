const fallback = {
  claimBoundary: "The reported counterexamples are external prior work. This page separately labels Lean-checked theorems, exact finite computations, mathematical candidates, refuted formulations, and unresolved steps.",
  lean: {
    moduleCount: 53,
    lastFailingModules: 0,
    trustBypasses: 0,
    finiteSuites: 12
  },
  claims: []
};

const statusStyles = {
  "finite-verified": "status-checked",
  "external-result": "status-open",
  "lean-checked": "status-checked",
  "mathematical-candidate": "status-candidate",
  "open": "status-open",
  "refuted": "status-refuted"
};

function escapeHtml(value) {
  return String(value)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}

function installSpectralResultLinks() {
  const nav = document.querySelector('nav[aria-label="Page contents"]');
  if (nav && !nav.querySelector('[data-spectral-link]')) {
    const link = document.createElement("a");
    link.href = "spectral-kernel.html";
    link.textContent = "Spectral kernel";
    link.dataset.spectralLink = "true";

    const checkedLink = nav.querySelector('a[href="#checked"]');
    nav.insertBefore(link, checkedLink);
  }

  const statusNote = document.querySelector(".status-note");
  if (statusNote && !document.getElementById("spectral-result-callout")) {
    const callout = document.createElement("section");
    callout.id = "spectral-result-callout";
    callout.className = "theorem candidate";

    const label = document.createElement("p");
    label.className = "theorem-label";
    label.textContent = "New structural result";

    const heading = document.createElement("h2");
    heading.textContent = "Spectral Frobenius-kernel resolution";

    const summary = document.createElement("p");
    summary.textContent = "A prime-uniform decomposition concentrates the kernel's nonfreeness in copies of the Frobenius ideal, predicts projective dimension p - 2 for p at least 3, and explains the ternary Hilbert numerator through three degree-three syzygies.";

    const action = document.createElement("p");
    const actionLink = document.createElement("a");
    actionLink.href = "spectral-kernel.html";
    actionLink.textContent = "Read the full spectral-kernel derivation";
    action.appendChild(actionLink);

    const scope = document.createElement("p");
    scope.className = "scope";
    scope.textContent = "Status: arithmetic core Lean checked; symbolic Betti identities verified; global module theorem awaiting full Lean formalization and independent review.";

    callout.append(label, heading, summary, action, scope);
    statusNote.insertAdjacentElement("afterend", callout);
  }
}

function render(data) {
  document.getElementById("claim-boundary").textContent = data.claimBoundary;
  document.getElementById("module-count").textContent = data.lean.moduleCount;
  document.getElementById("failure-count").textContent = data.lean.lastFailingModules;
  document.getElementById("trust-count").textContent = data.lean.trustBypasses;
  document.getElementById("suite-count").textContent = data.lean.finiteSuites;

  const container = document.getElementById("claim-cards");
  container.innerHTML = data.claims.map(claim => {
    const statusClass = statusStyles[claim.status] || "status-open";
    const statusLabel = claim.status.replaceAll("-", " ");
    const detailLink = claim.url
      ? `<p><a href="${escapeHtml(claim.url)}">Read the detailed derivation</a></p>`
      : "";
    return `
      <article class="claim-entry">
        <div class="claim-status ${escapeHtml(statusClass)}">${escapeHtml(statusLabel)}</div>
        <div class="claim-copy">
          <h3>${escapeHtml(claim.name)}</h3>
          <p>${escapeHtml(claim.evidence)}</p>
          ${detailLink}
        </div>
      </article>`;
  }).join("");
}

installSpectralResultLinks();

fetch("status.json", { cache: "no-store" })
  .then(response => {
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.json();
  })
  .then(render)
  .catch(error => {
    console.error("Status load failed", error);
    render(fallback);
  });
