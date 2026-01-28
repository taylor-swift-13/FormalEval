Example problem_70_test :
  problem_70_spec
    [1%Z; 2%Z; 3%Z; 4%Z]
    [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  unfold problem_70_spec, strange_sort_list.
  vm_compute.
  reflexivity.
Qed.