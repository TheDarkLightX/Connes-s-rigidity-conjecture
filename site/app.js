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
