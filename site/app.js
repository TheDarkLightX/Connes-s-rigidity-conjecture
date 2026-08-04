const fallback = {
  claimBoundary: "Two distinct counterexamples are publicly claimed; a recent adversarial manuscript disputes them but presently addresses different groups. This site presents unreviewed prime-uniform proof candidates and claims neither priority nor independently settled final status.",
  lean: { moduleCount: 51, lastFailingModules: 6 },
  claims: []
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
    const statusClass = `status-${claim.status}`;
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
