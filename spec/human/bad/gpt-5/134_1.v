Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Lia.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

Definition space : ascii := Ascii.ascii_of_nat 32.

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122).

Definition ends_with_single_letter_pred (s : string) : Prop :=
  let l := list_ascii_of_string s in
  exists (pre : list ascii) (c : ascii),
    l = pre ++ [c] /\
    is_alpha c /\
    (pre = [] \/ exists (pre' : list ascii), pre = pre' ++ [space]).

Definition problem_134_pre (s : string) : Prop := True.

Definition problem_134_spec (s : string) (b : bool) : Prop :=
  b = true <-> ends_with_single_letter_pred s.

Example problem_134_example_apple :
  problem_134_spec "apple" false.
Proof.
  unfold problem_134_spec.
  split.
  - intro H. discriminate H.
  - intro H. exfalso.
    unfold ends_with_single_letter_pred in H.
    simpl in H.
    destruct H as [pre [c [Heq [Halpha Hpre]]]].
    (* pre ++ [c] = ["a";"p";"p";"l";"e"] *)
    destruct pre as [|x1 pre1].
    + simpl in Heq. discriminate Heq.
    + simpl in Heq. rewrite app_comm_cons in Heq.
      inversion Heq as [Hx1a Heq1]. subst x1.
      destruct pre1 as [|x2 pre2].
      * simpl in Heq1. discriminate Heq1.
      * simpl in Heq1. rewrite app_comm_cons in Heq1.
        inversion Heq1 as [Hx2p Heq2]. subst x2.
        destruct pre2 as [|x3 pre3].
        -- simpl in Heq2. discriminate Heq2.
        -- simpl in Heq2. rewrite app_comm_cons in Heq2.
           inversion Heq2 as [Hx3p Heq3]. subst x3.
           destruct pre3 as [|x4 pre4].
           ++ simpl in Heq3. discriminate Heq3.
           ++ simpl in Heq3. rewrite app_comm_cons in Heq3.
              inversion Heq3 as [Hx4l Heq4]. subst x4.
              destruct pre4 as [|x5 pre5].
              ** simpl in Heq4.
                 inversion Heq4 as [Hc_e Hnil]. subst c.
                 destruct Hpre as [Hpre_empty | [pre' Hpre_space]].
                 --- discriminate Hpre_empty.
                 --- set (Hps := Hpre_space). clear Hpre_space.
                     change pre with ("a"%char :: "p"%char :: "p"%char :: "l"%char :: []) in Hps.
                     (* Hps : pre' ++ [space] = ["a";"p";"p";"l"] *)
                     destruct pre' as [|y1 pre1'].
                     + simpl in Hps. inversion Hps as [Hspace_eq_a Hrest].
                       apply f_equal nat_of_ascii in Hspace_eq_a.
                       simpl in Hspace_eq_a. lia.
                     + simpl in Hps. rewrite app_comm_cons in Hps.
                       inversion Hps as [Hy1a Hps1]. subst y1.
                       destruct pre1' as [|y2 pre2'].
                       * simpl in Hps1. rewrite app_comm_cons in Hps1.
                         inversion Hps1 as [Hy2p Hps2]. subst y2.
                         destruct pre2' as [|y3 pre3'].
                         -- simpl in Hps2. rewrite app_comm_cons in Hps2.
                            inversion Hps2 as [Hy3p Hps3]. subst y3.
                            destruct pre3' as [|y4 pre4'].
                            ** simpl in Hps3.
                               inversion Hps3 as [Hspace_eq_l Hnil2].
                               apply f_equal nat_of_ascii in Hspace_eq_l.
                               simpl in Hspace_eq_l. lia.
                            ** simpl in Hps3. discriminate Hps3.
                         -- simpl in Hps2. discriminate Hps2.
                       * simpl in Hps1. discriminate Hps1.
              ** simpl in Heq4. discriminate Heq4.
Qed.