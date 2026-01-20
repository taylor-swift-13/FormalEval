Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Psatz.

Local Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res =
    orb
      (orb (if Req_EM_T (a * a + b * b) (c * c) then true else false)
           (if Req_EM_T (a * a + c * c) (b * b) then true else false))
      (if Req_EM_T (b * b + c * c) (a * a) then true else false).

Example right_angle_triangle_spec_94_82545294464254_26_117120159873124_94_48837938393268 :
  right_angle_triangle_spec 94.82545294464254%R 26.117120159873124%R 94.48837938393268%R false.
Proof.
  unfold right_angle_triangle_spec.
  assert (H1pos : 94.82545294464254%R * 94.82545294464254%R
                  + 26.117120159873124%R * 26.117120159873124%R
                  - 94.48837938393268%R * 94.48837938393268%R > 0) by nra.
  assert (H2pos : 94.82545294464254%R * 94.82545294464254%R
                  + 94.48837938393268%R * 94.48837938393268%R
                  - 26.117120159873124%R * 26.117120159873124%R > 0) by nra.
  assert (H3pos : 26.117120159873124%R * 26.117120159873124%R
                  + 94.48837938393268%R * 94.48837938393268%R
                  - 94.82545294464254%R * 94.82545294464254%R > 0) by nra.
  assert (H1ne :
            94.82545294464254%R * 94.82545294464254%R
            + 26.117120159873124%R * 26.117120159873124%R
            <> 94.48837938393268%R * 94.48837938393268%R).
  { intro Heq. rewrite Heq in H1pos. lra. }
  assert (H2ne :
            94.82545294464254%R * 94.82545294464254%R
            + 94.48837938393268%R * 94.48837938393268%R
            <> 26.117120159873124%R * 26.117120159873124%R).
  { intro Heq. rewrite Heq in H2pos. lra. }
  assert (H3ne :
            26.117120159873124%R * 26.117120159873124%R
            + 94.48837938393268%R * 94.48837938393268%R
            <> 94.82545294464254%R * 94.82545294464254%R).
  { intro Heq. rewrite Heq in H3pos. lra. }
  assert (E1 :
            (if Req_EM_T
                 (94.82545294464254%R * 94.82545294464254%R
                  + 26.117120159873124%R * 26.117120159873124%R)
                 (94.48837938393268%R * 94.48837938393268%R)
             then true else false) = false).
  { destruct (Req_EM_T
                (94.82545294464254%R * 94.82545294464254%R
                 + 26.117120159873124%R * 26.117120159873124%R)
                (94.48837938393268%R * 94.48837938393268%R)) as [Heq|Hneq].
    - exfalso; apply H1ne; exact Heq.
    - reflexivity.
  }
  assert (E2 :
            (if Req_EM_T
                 (94.82545294464254%R * 94.82545294464254%R
                  + 94.48837938393268%R * 94.48837938393268%R)
                 (26.117120159873124%R * 26.117120159873124%R)
             then true else false) = false).
  { destruct (Req_EM_T
                (94.82545294464254%R * 94.82545294464254%R
                 + 94.48837938393268%R * 94.48837938393268%R)
                (26.117120159873124%R * 26.117120159873124%R)) as [Heq|Hneq].
    - exfalso; apply H2ne; exact Heq.
    - reflexivity.
  }
  assert (E3 :
            (if Req_EM_T
                 (26.117120159873124%R * 26.117120159873124%R
                  + 94.48837938393268%R * 94.48837938393268%R)
                 (94.82545294464254%R * 94.82545294464254%R)
             then true else false) = false).
  { destruct (Req_EM_T
                (26.117120159873124%R * 26.117120159873124%R
                 + 94.48837938393268%R * 94.48837938393268%R)
                (94.82545294464254%R * 94.82545294464254%R)) as [Heq|Hneq].
    - exfalso; apply H3ne; exact Heq.
    - reflexivity.
  }
  rewrite E1, E2, E3.
  simpl.
  reflexivity.
Qed.