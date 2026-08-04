const fallback = {
  claimBoundary: "The broad rigidity conjecture was disproved in 2026. This repository distinguishes checked companion theorems, finite computations, and unreviewed proof candidates.",
  lean: { moduleCount: 51, fullBuild: "pending" },
  claims: []
};

const statusStyles = {
  "finite-verified": "status-checked",
  "external-result": "status-checked",
  "source-under-validation": "status-under-repair",
  "paper-proof-candidate": "status-under-repair",
  "conjecture": "status-open",
  "under-repair": "status-under-repair",
  "open": "status-open",
  "refuted": "status-refuted",
  "checked": "status-checked"
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

  const container = document.getElementById("claim-cards");
  container.innerHTML = data.claims.map(claim => {
    const statusClass = statusStyles[claim.status] || "status-open";
    return `
      <article class="claim-card">
        <span class="status-pill ${escapeHtml(statusClass)}">${escapeHtml(claim.status.replaceAll("-", " "))}</span>
        <h3>${escapeHtml(claim.name)}</h3>
        <p>${escapeHtml(claim.evidence)}</p>
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
