Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition substring (s sub : string) : Prop :=
  exists l r, s = String.append l (String.append sub r).

Definition rotation_of (b rot : string) : Prop :=
  exists x y, b = String.append x y /\ rot = String.append y x.

Definition cycpattern_check_spec (a b : string) (res : bool) : Prop :=
  res = true <->
    a = b \/
    b = EmptyString \/
    exists rot, rotation_of b rot /\ substring a rot.

Example test_case : cycpattern_check_spec "xyzw" "xyw" false.
Proof.
  unfold cycpattern_check_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | H]].
    + inversion H.
    + inversion H.
    + destruct H as [rot [Hrot Hsub]].
      unfold rotation_of in Hrot.
      destruct Hrot as [x [y [Hb Hrot]]].
      (* Helper tactic to solve string mismatches *)
      let solve_str := 
        simpl in *;
        repeat match goal with
        | H: String _ _ = String _ _ |- _ => inversion H; subst; clear H
        end
      in
      destruct x as [|c1 x].
      * (* x = "" *)
        simpl in Hb. subst y. simpl in Hrot. subst rot.
        unfold substring in Hsub. destruct Hsub as [l [r Hsub]].
        destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l]]];
        solve_str.
      * destruct x as [|c2 x].
        -- (* x has 1 char *)
           simpl in Hb. inversion Hb. subst y. simpl in Hrot. subst rot.
           unfold substring in Hsub. destruct Hsub as [l [r Hsub]].
           destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l]]];
           solve_str.
        -- destruct x as [|c3 x].
           ++ (* x has 2 chars *)
              simpl in Hb. inversion Hb. subst y. simpl in Hrot. subst rot.
              unfold substring in Hsub. destruct Hsub as [l [r Hsub]].
              destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l]]];
              solve_str.
           ++ destruct x as [|c4 x].
              ** (* x has 3 chars *)
                 simpl in Hb. inversion Hb. subst y. simpl in Hrot. 
                 rewrite String.append_nil_r in Hrot. subst rot.
                 unfold substring in Hsub. destruct Hsub as [l [r Hsub]].
                 destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l as [|? l]; [|destruct l]]];
                 solve_str.
              ** (* x has >= 4 chars *)
                 simpl in Hb. inversion Hb.
Qed.