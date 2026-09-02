#!/usr/bin/env bash
# verify.sh — INDEPENDENT kernel check. Run this yourself; it trusts no prose.
# It asks Lean directly whether the claims hold. Usage:  bash verify.sh
set -uo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

echo "============================================================"
echo " 1. lake build ALL modules — the kernel is the arbiter (want: 'Build completed successfully')"
echo "    (builds every module, not just the root closure — leaf files like"
echo "     IntegrateTheorem are outside it and would otherwise hide breakage)"
echo "============================================================"
ls Concentricity/*.lean | sed 's|Concentricity/|Concentricity.|; s|\.lean||' | xargs lake build 2>&1 | tail -4

echo
echo "============================================================"
echo " 2. sorries / escape hatches in the SOURCE (want: none; zero sorries since 2026-09-02)"
echo "============================================================"
# Match `sorry`/`admit` only where it is a term or tactic (same shape as
# .githooks/pre-commit), never inside prose: a bare line, `:= sorry`,
# `by sorry`, `, sorry`, `(sorry`.
grep -rnE '^[[:space:]]*(sorry|admit)[[:space:]]*$|:=[[:space:]]*(sorry|admit)([^[:alnum:]_]|$)|by[[:space:]]+(sorry|admit)([^[:alnum:]_]|$)|,[[:space:]]*(sorry|admit)([^[:alnum:]_]|$)|\([[:space:]]*(sorry|admit)([^[:alnum:]_]|$)|native_decide' Concentricity/*.lean \
  | grep -vE ':[0-9]+:[[:space:]]*--' || echo "  (none found in code)"

echo
echo "============================================================"
echo " 3. DECLARED axioms in the project (R9 target: zero)"
echo "============================================================"
grep -rnE '^axiom ' Concentricity/*.lean || echo "  (none — no project axioms declared)"

echo
echo "============================================================"
echo " 4. Lean prints the headline STATEMENTS and their AXIOMS itself"
echo "    (synchronized 2026-09-02: zeta concentricity <-> RH, the conditional"
echo "     half-centre, and the nonconcentric A-section; the former universal"
echo "     theorem ASection.concentricity was withdrawn as false)."
echo "    sorryAx here => there is a real gap somewhere in the proof tree."
echo "============================================================"
cat > Concentricity/_Verify.lean <<'EOF'
import Concentricity.Corollaries
import Concentricity.SpecCandidate
#check @zetaSection_concentric_iff_RH
#check @zetaSection_pairwiseTransportLevel_iff_RH
#check @zetaSection_sphereZero_re_eq_half_of_RH
#check @SpecCandidate.current_ASection_concentricity_type_false
#print axioms zetaSection_concentric_iff_RH
#print axioms zetaSection_pairwiseTransportLevel_iff_RH
#print axioms zetaSection_sphereZero_re_eq_half_of_RH
#print axioms zetaSection_transportLevel_eq_half_of_RH
#print axioms zeta_criticalLine_zeros_infinite_of_RH
#print axioms SpecCandidate.current_ASection_concentricity_type_false
EOF
lake build Concentricity._Verify 2>&1 \
  | grep -iE '_iff_RH :|_of_RH :|_type_false :|depends on axioms' || echo "  (build failed — see 'lake build Concentricity._Verify')"
rm -f Concentricity/_Verify.lean

echo
echo "Done. You verified this against the kernel, not against anything I told you."
