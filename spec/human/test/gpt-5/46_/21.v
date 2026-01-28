Require Import Coq.Arith.Arith.

(* 使用归纳关系表示 fib4 序列*)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

(* Pre: no additional constraints for `fib4` *)
Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

Example problem_46_test : problem_46_spec 22 273282.
Proof.
  unfold problem_46_spec.
  assert (h4: fib4_at 4 2).
  { eapply fib4_at_SSSS with (i:=0) (a:=0) (b:=0) (c:=2) (d:=0).
    - exact fib4_at_0.
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3.
  }
  assert (h5: fib4_at 5 4).
  { eapply fib4_at_SSSS with (i:=1) (a:=0) (b:=2) (c:=0) (d:=2).
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact h4.
  }
  assert (h6: fib4_at 6 8).
  { eapply fib4_at_SSSS with (i:=2) (a:=2) (b:=0) (c:=2) (d:=4).
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact h4.
    - exact h5.
  }
  assert (h7: fib4_at 7 14).
  { eapply fib4_at_SSSS with (i:=3) (a:=0) (b:=2) (c:=4) (d:=8).
    - exact fib4_at_3.
    - exact h4.
    - exact h5.
    - exact h6.
  }
  assert (h8: fib4_at 8 28).
  { eapply fib4_at_SSSS with (i:=4) (a:=2) (b:=4) (c:=8) (d:=14).
    - exact h4.
    - exact h5.
    - exact h6.
    - exact h7.
  }
  assert (h9: fib4_at 9 54).
  { eapply fib4_at_SSSS with (i:=5) (a:=4) (b:=8) (c:=14) (d:=28).
    - exact h5.
    - exact h6.
    - exact h7.
    - exact h8.
  }
  assert (h10: fib4_at 10 104).
  { eapply fib4_at_SSSS with (i:=6) (a:=8) (b:=14) (c:=28) (d:=54).
    - exact h6.
    - exact h7.
    - exact h8.
    - exact h9.
  }
  assert (h11: fib4_at 11 200).
  { eapply fib4_at_SSSS with (i:=7) (a:=14) (b:=28) (c:=54) (d:=104).
    - exact h7.
    - exact h8.
    - exact h9.
    - exact h10.
  }
  assert (h12: fib4_at 12 386).
  { eapply fib4_at_SSSS with (i:=8) (a:=28) (b:=54) (c:=104) (d:=200).
    - exact h8.
    - exact h9.
    - exact h10.
    - exact h11.
  }
  assert (h13: fib4_at 13 744).
  { eapply fib4_at_SSSS with (i:=9) (a:=54) (b:=104) (c:=200) (d:=386).
    - exact h9.
    - exact h10.
    - exact h11.
    - exact h12.
  }
  assert (h14: fib4_at 14 1434).
  { eapply fib4_at_SSSS with (i:=10) (a:=104) (b:=200) (c:=386) (d:=744).
    - exact h10.
    - exact h11.
    - exact h12.
    - exact h13.
  }
  assert (h15: fib4_at 15 2764).
  { eapply fib4_at_SSSS with (i:=11) (a:=200) (b:=386) (c:=744) (d:=1434).
    - exact h11.
    - exact h12.
    - exact h13.
    - exact h14.
  }
  assert (h16: fib4_at 16 5328).
  { eapply fib4_at_SSSS with (i:=12) (a:=386) (b:=744) (c:=1434) (d:=2764).
    - exact h12.
    - exact h13.
    - exact h14.
    - exact h15.
  }
  assert (h17: fib4_at 17 10270).
  { eapply fib4_at_SSSS with (i:=13) (a:=744) (b:=1434) (c:=2764) (d:=5328).
    - exact h13.
    - exact h14.
    - exact h15.
    - exact h16.
  }
  assert (h18: fib4_at 18 19796).
  { eapply fib4_at_SSSS with (i:=14) (a:=1434) (b:=2764) (c:=5328) (d:=10270).
    - exact h14.
    - exact h15.
    - exact h16.
    - exact h17.
  }
  assert (h19: fib4_at 19 38158).
  { eapply fib4_at_SSSS with (i:=15) (a:=2764) (b:=5328) (c:=10270) (d:=19796).
    - exact h15.
    - exact h16.
    - exact h17.
    - exact h18.
  }
  assert (h20: fib4_at 20 73552).
  { eapply fib4_at_SSSS with (i:=16) (a:=5328) (b:=10270) (c:=19796) (d:=38158).
    - exact h16.
    - exact h17.
    - exact h18.
    - exact h19.
  }
  assert (h21: fib4_at 21 141776).
  { eapply fib4_at_SSSS with (i:=17) (a:=10270) (b:=19796) (c:=38158) (d:=73552).
    - exact h17.
    - exact h18.
    - exact h19.
    - exact h20.
  }
  assert (h22: fib4_at 22 273282).
  { eapply fib4_at_SSSS with (i:=18) (a:=19796) (b:=38158) (c:=73552) (d:=141776).
    - exact h18.
    - exact h19.
    - exact h20.
    - exact h21.
  }
  exact h22.
Qed.