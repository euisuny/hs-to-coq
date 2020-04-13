Require Import DeepWeb.Spec.TopLevelProp.
Require Import DeepWeb.Spec.Swap_ImplModel.

From DeepWeb.Spec.Vst
     Require Import MainInit Gprog SocketSpecs
     MonadExports LibrarySpecs
     zeroize_addr_spec bind_socket_spec new_store_spec init_store_spec
     new_connection_spec reset_connection_spec
     populate_response_spec check_if_complete_spec
     accept_connection_spec conn_read_spec conn_write_spec
     process_spec add_to_fd_set_spec
     monitor_connections_spec process_connections_spec
     select_loop_spec.

From DeepWeb.Proofs.Vst
     Require Import verif_main verif_zeroize_addr verif_bind_socket
     verif_new_store verif_init_store verif_new_connection
     verif_reset_connection
     verif_populate_response verif_check_if_complete
     verif_accept_connection verif_conn_read verif_conn_write
     verif_process verif_add_to_fd_set verif_monitor_connections
     verif_process_connections verif_select_loop.

Ltac unify_spec :=
  match goal with
  | [H: semax_body _ _ _ ?spec1 |- semax_body _ _ _ ?spec2] =>
    replace spec2 with spec1;
    [apply H |];
    unfold NDmk_funspec;
    try unfold spec1;
    f_equal
  end.

Ltac extract_ret_val :=
  match goal with
  | [|- context[PROPx _ (LOCALx [temp _ _] _) ]] =>
    let H := fresh "Hret" in
    rewrite <- insert_local;
    rewrite lower_andp;
    apply derives_extract_prop; intro H;
    destruct H as [H1 H2]; unfold_lift in H1;
    rewrite retval_ext_rval in H1
  end.

Ltac lower_to_SEP :=
  match goal with
  | |- context[PROPx _ (LOCALx _ (SEPx ?sep)) ?rho |-- ?rhs] =>
    let H := fresh "Hlower" in
    pose proof (finish_lower rho (fun _ => True) sep rhs) as H;
    rewrite <- local_andp_lemma in H by (apply local_True_right);
    apply H; clear H;
    intros _; simpl
  end.

Ltac my_semax_func_cons_ext PD :=
  eapply semax_func_cons_ext;
  [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | semax_func_cons_ext_tc;
      try solve [ (*THIS LINE IS NEW*) simpl; repeat (apply exp_left; intros);
                  apply typecheck_return_value; auto]
    | solve[ first [eapply semax_ext;
                    [ (*repeat first [reflexivity | left; reflexivity | right]*)
                      try solve [unfold ext_link_prog; rewrite PD;
                                 apply from_elements_In; reflexivity]
                    | apply extcall_lemmas.compute_funspecs_norepeat_e;
                      reflexivity
                    | reflexivity
                    | reflexivity ]]]
      || fail "Try 'eapply semax_func_cons_ext.'"
              "To solve [semax_external] judgments, do 'eapply semax_ext.'"
              "Make sure that the Espec declared using 'Existing Instance'
               is defined as 'add_funspecs NullExtension.Espec Gprog.'"
    |
  ].

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.

  assert (PD: prog_defs prog = global_definitions) by reflexivity.
  unfold prog_funct.
  
  rewrite PD.
  
  repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).

  semax_func_cons body_malloc.
  apply semax_func_cons_malloc_aux.
 
  my_semax_func_cons_ext PD. 
  
  my_semax_func_cons_ext PD.
  
  { (* typechecking for memcpy *)
    extract_ret_val.
    subst v.
    lower_to_SEP.
    entailer!.
  } 
  
  my_semax_func_cons_ext PD.
  
  { (* typechecking for memset *)
    extract_ret_val.
    subst v.
    lower_to_SEP.
    entailer!.
  } 
  
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD.
  my_semax_func_cons_ext PD. 
  my_semax_func_cons_ext PD.
  
  { (* typechecking for htons *)
    extract_ret_val.
    rewrite <- H1.

    match goal with
    | |- context[(PROPx (?prop :: ?other_prop) ?rest) ?rho |-- ?rhs] =>
      apply (derives_extract_PROP' prop other_prop
                                   rest (fun _ => rhs))
    end.

    intros bound.
    simpl.
    intros e.
    entailer!.
    simpl in bound.
    rewrite Int.unsigned_repr; rep_omega.
  } 

  (* select *)
  my_semax_func_cons_ext PD. 
  
  semax_func_cons body_fd_zero_macro.
  semax_func_cons body_fd_isset_macro.
  semax_func_cons body_fd_set_macro.
  semax_func_cons body_check_if_complete.
  semax_func_cons body_new_connection.
  semax_func_cons body_new_store.
  semax_func_cons body_populate_response.
  semax_func_cons body_conn_read.
  semax_func_cons body_reset_connection.
  semax_func_cons body_conn_write.
  semax_func_cons body_process.
  semax_func_cons body_accept_connection.
  semax_func_cons body_add_to_fd_set.
  semax_func_cons body_monitor_connections.
  semax_func_cons body_process_connections.

  apply semax_func_cons.
  { auto. }
  { apply Forall_cons; auto.
    apply Forall_cons; auto.
  } 
  { unfold var_sizes_ok.
    repeat (apply Forall_cons; [simpl; rep_omega | ]).
    constructor.
  } 
  { auto. }
  { precondition_closed. } 
  { pose proof body_select_loop.
    unfold select_loop_spec in H.
    unify_spec.
  } 

  semax_func_cons body_zeroize_addr.

  apply semax_func_cons.
  { auto. }
  { apply Forall_cons; auto. } 
  { repeat (apply Forall_cons; [simpl; rep_omega | ]).
    constructor.
  } 
  { auto. }
  { precondition_closed. } 
  {
    pose proof body_bind_socket.
    unfold bind_socket_spec in H.
    unify_spec.
  }

  semax_func_cons body_init_store.
  semax_func_cons body_main.
  
Qed.

Theorem prog_correct: semax_prog_ext prog real_swap_impl Vprog Gprog.
Proof.
  Local Ltac final_tac := apply all_funcs_correct.

  prove_semax_prog_aux final_tac.

Qed.