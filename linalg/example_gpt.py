def calculate_step():
    n_embd = state_dict["wte"].shape[1]
    head_dim = n_embd // n_head
    head_scale = head_dim**0.5

    state_dict["tok_emb_0"] = E("i->i", state_dict["wte"][token_id])
    state_dict["pos_emb_0"] = E("i->i", state_dict["wpe"][pos_id])
    state_dict["joint_emb_0"] = state_dict["tok_emb_0"] + state_dict["pos_emb_0"]
    state_dict["block_input_0"] = rmsnorm(state_dict["joint_emb_0"])

    for li in range(n_layer):
        state_dict[f"layer{li}.attn_residual"] = E("i->i", state_dict[f"block_input_{li}"])
        state_dict[f"layer{li}.attn_norm"] = rmsnorm(state_dict[f"block_input_{li}"])
        state_dict[f"layer{li}.q_head"] = E("hjd,d->hj", state_dict[f"layer{li}.attn_wq_head"], state_dict[f"layer{li}.attn_norm"])
        state_dict[f"layer{li}.k_head"] = E("hjd,d->hj", state_dict[f"layer{li}.attn_wk_head"], state_dict[f"layer{li}.attn_norm"])
        state_dict[f"layer{li}.v_head"] = E("hjd,d->hj", state_dict[f"layer{li}.attn_wv_head"], state_dict[f"layer{li}.attn_norm"])

        keys[pos_id, li, :, :] = state_dict[f"layer{li}.k_head"]
        values[pos_id, li, :, :] = state_dict[f"layer{li}.v_head"]

        state_dict[f"layer{li}.key_prefix"] = E("thj->thj", keys[:, li, :, :])
        state_dict[f"layer{li}.value_prefix"] = E("thj->thj", values[:, li, :, :])

        state_dict[f"layer{li}.attn_logits"] = E("hj,thj->ht", state_dict[f"layer{li}.q_head"], state_dict[f"layer{li}.key_prefix"]) / head_scale
        state_dict[f"layer{li}.attn_weights"] = softmax_last(state_dict[f"layer{li}.attn_logits"])
        state_dict[f"layer{li}.head_output"] = E("ht,thj->hj", state_dict[f"layer{li}.attn_weights"], state_dict[f"layer{li}.value_prefix"])
        state_dict[f"layer{li}.attn_projected"] = E("ohj,hj->o", state_dict[f"layer{li}.attn_wo_head"], state_dict[f"layer{li}.head_output"])
        state_dict[f"layer{li}.attn_output"] = state_dict[f"layer{li}.attn_projected"] + state_dict[f"layer{li}.attn_residual"]

        state_dict[f"layer{li}.mlp_residual"] = E("i->i", state_dict[f"layer{li}.attn_output"])
        state_dict[f"layer{li}.mlp_norm"] = rmsnorm(state_dict[f"layer{li}.attn_output"])
        state_dict[f"layer{li}.mlp_fc1_out"] = E("od,d->o", state_dict[f"layer{li}.mlp_fc1"], state_dict[f"layer{li}.mlp_norm"])
        state_dict[f"layer{li}.mlp_relu"] = np.maximum(state_dict[f"layer{li}.mlp_fc1_out"], 0.0)
        state_dict[f"layer{li}.mlp_fc2_out"] = E("od,d->o", state_dict[f"layer{li}.mlp_fc2"], state_dict[f"layer{li}.mlp_relu"])
        state_dict[f"layer{li}.block_output"] = state_dict[f"layer{li}.mlp_fc2_out"] + state_dict[f"layer{li}.mlp_residual"]

        if li + 1 < n_layer:
            state_dict[f"block_input_{li + 1}"] = E("i->i", state_dict[f"layer{li}.block_output"])

    state_dict["final_x_0"] = E("i->i", state_dict["block_input_0"]) if n_layer == 0 else E("i->i", state_dict[f"layer{n_layer - 1}.block_output"])
    state_dict["final_x_1"] = E("i->i", state_dict["final_x_0"])
    state_dict["logits_0"] = E("od,d->o", state_dict["lm_head"], state_dict["final_x_1"])
    return state_dict["logits_0"]
