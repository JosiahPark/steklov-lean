# Lean verification status: FAIL

Checked 2026-11-04 11:27 UTC. 0 of 190 theorems compile with only Lean's standard axioms.

Scope: these are the algebraic, geometric and limit-assembly lemmas. The main theorem (Theorem 1.3 / 11.1)
is NOT certified: `sharp_integer_law_of_two_scale` and `sharp_real_law_of_two_scale` take the analytic
two-scale bound as a hypothesis, and no Dirichlet-to-Neumann operator is defined in Lean.

Named hypotheses behind the conditional main theorem (`MainConditional.lean`): 0. The goal is to shrink this list.


Escape hatches (sorry, admit, axiom, maxHeartbeats, native_decide, unsafe, opaque): none

| File | Theorem | Result |
|---|---|---|
| Algebra.lean | `SteklovAudit.tetra_face_count` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.tetra_edge_count` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.tetra_surface_area` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.tetra_half_angle_sin_sq` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.bounded_shift_changes_linear_term` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.six_edge_contribution` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.scale_rho_lt_half` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.scale_sigma_lt_rho` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.scale_dwell_exponent` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.scale_collar_over_dwell_exponent` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.scale_uncertainty_over_dwell_exponent` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.hyperbolic_subtraction` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.dihedral_integrand_algebra` | NOT CHECKED (name not found by Lean) |
| Algebra.lean | `SteklovAudit.right_angle_integrand` | NOT CHECKED (name not found by Lean) |
| Geometry.lean | `SteklovAudit.rotation_fixed_vector_zero` | NOT CHECKED (name not found by Lean) |
| Geometry.lean | `SteklovAudit.reflection_fixed_vector_axis` | NOT CHECKED (name not found by Lean) |
| Geometry.lean | `SteklovAudit.translation_return` | NOT CHECKED (name not found by Lean) |
| Geometry.lean | `SteklovAudit.translation_return_parallel` | NOT CHECKED (name not found by Lean) |
| Geometry.lean | `SteklovAudit.reflection_return_velocity` | NOT CHECKED (name not found by Lean) |
| Tauberian.lean | `SteklovAudit.dyadic_sum` | NOT CHECKED (name not found by Lean) |
| Tauberian.lean | `SteklovAudit.dyadic_sum_le_two` | NOT CHECKED (name not found by Lean) |
| Tauberian.lean | `SteklovAudit.bounded_shift_can_change_linear` | NOT CHECKED (name not found by Lean) |
| Tauberian.lean | `SteklovAudit.squared_partition_scalar` | NOT CHECKED (name not found by Lean) |
| Tauberian.lean | `SteklovAudit.ordered_two_scale_limit` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.symmetric_weyl_window` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.interval_mass_polynomial` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.two_error_composition` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.linear_coefficient_under_shift` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.first_riesz_coefficients` | NOT CHECKED (name not found by Lean) |
| WindowArithmetic.lean | `SteklovAudit.choose_scales` | NOT CHECKED (name not found by Lean) |
| FiniteWindowMass.lean | `SteklovAudit.finite_mass_weight_bound` | NOT CHECKED (name not found by Lean) |
| FiniteWindowMass.lean | `SteklovAudit.spectral_window_polynomial_decomposition` | NOT CHECKED (name not found by Lean) |
| WholeTheorem.lean | `SteklovAudit.sharp_integer_law_of_two_scale` | NOT CHECKED (name not found by Lean) |
| RealAxisAssembly.lean | `SteklovAudit.sharp_real_law_of_two_scale` | NOT CHECKED (name not found by Lean) |
| RealAxisAssembly.lean | `SteklovAudit.one_step_polynomial_change` | NOT CHECKED (name not found by Lean) |
| Section5Scaling.lean | `SteklovAudit.scaled_strip_window` | NOT CHECKED (name not found by Lean) |
| Section5Scaling.lean | `SteklovAudit.cone_ball_window` | NOT CHECKED (name not found by Lean) |
| Section5Scaling.lean | `SteklovAudit.symmetric_band_width` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSums.lean | `SteklovAudit.positive_mass_signed_kernel_bound` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSums.lean | `SteklovAudit.unit_window_linear_decomposition` | NOT CHECKED (name not found by Lean) |
| Section10FiniteDirections.lean | `SteklovAudit.translation_velocity_collinear` | NOT CHECKED (name not found by Lean) |
| Section10FiniteDirections.lean | `SteklovAudit.nontrivial_rotation_immobile` | NOT CHECKED (name not found by Lean) |
| Section11Partition.lean | `SteklovAudit.finite_partition_error` | NOT CHECKED (name not found by Lean) |
| Section11Partition.lean | `SteklovAudit.real_weyl_partition_identity` | NOT CHECKED (name not found by Lean) |
| Section11Partition.lean | `SteklovAudit.small_two_parameter_budget` | NOT CHECKED (name not found by Lean) |
| Section7SchwartzFinite.lean | `SteklovAudit.finite_schwartz_window_bound` | NOT CHECKED (name not found by Lean) |
| SmoothedBridge.lean | `SteklovAudit.sharp_count_of_smoothed_and_unsmoothing` | NOT CHECKED (name not found by Lean) |
| Section7ExplicitBarrier.lean | `SteklovAudit.explicit_barrier_numerator` | NOT CHECKED (name not found by Lean) |
| Section7ExplicitBarrier.lean | `SteklovAudit.improved_barrier_numerator` | NOT CHECKED (name not found by Lean) |
| Section11RegionAssembly.lean | `SteklovAudit.three_region_remainder` | NOT CHECKED (name not found by Lean) |
| Section11RegionAssembly.lean | `SteklovAudit.total_error_from_three_regions` | NOT CHECKED (name not found by Lean) |
| Section11RegionAssembly.lean | `SteklovAudit.real_sharp_law_if_partition_bounds` | NOT CHECKED (name not found by Lean) |
| FiniteSpectralTrace.lean | `SteklovAudit.finite_eigenstate_squared_partition` | NOT CHECKED (name not found by Lean) |
| FiniteSpectralTrace.lean | `SteklovAudit.finite_spectral_trace_squared_partition` | NOT CHECKED (name not found by Lean) |
| FiniteSpectralTrace.lean | `SteklovAudit.finite_local_spectral_mass_nonneg` | NOT CHECKED (name not found by Lean) |
| FiniteSpectralTrace.lean | `SteklovAudit.finite_local_count_identity` | NOT CHECKED (name not found by Lean) |
| Section7PolynomialDuhamel.lean | `SteklovAudit.polynomial_duhamel_identity` | NOT CHECKED (name not found by Lean) |
| Section7PolynomialDuhamel.lean | `SteklovAudit.intertwines_all_powers` | NOT CHECKED (name not found by Lean) |
| Section7PolynomialDuhamel.lean | `SteklovAudit.polynomial_duhamel_contraction_bound` | NOT CHECKED (name not found by Lean) |
| Section7TaylorDuhamel.lean | `SteklovAudit.truncated_exp_quasicommutator` | NOT CHECKED (name not found by Lean) |
| Section7TaylorDuhamel.lean | `SteklovAudit.truncated_exp_exact_intertwiner` | NOT CHECKED (name not found by Lean) |
| Section7HSTails.lean | `SteklovAudit.finite_hs_tail_le_total` | NOT CHECKED (name not found by Lean) |
| Section7HSTails.lean | `SteklovAudit.finite_hs_tail_vanishes` | NOT CHECKED (name not found by Lean) |
| Section9PropagationScales.lean | `SteklovAudit.section9_exponent_positivity` | NOT CHECKED (name not found by Lean) |
| Section9PropagationScales.lean | `SteklovAudit.section9_example_exponents` | NOT CHECKED (name not found by Lean) |
| Section9CellBudget.lean | `SteklovAudit.finite_phase_cell_error_budget` | NOT CHECKED (name not found by Lean) |
| Section7RelativeFinite.lean | `SteklovAudit.finite_relative_inverse_trace` | NOT CHECKED (name not found by Lean) |
| Section7RelativeFinite.lean | `SteklovAudit.finite_spectral_count_below_bottom` | NOT CHECKED (name not found by Lean) |
| Section7OffBandIteration.lean | `SteklovAudit.offBandStep_difference` | NOT CHECKED (name not found by Lean) |
| Section7OffBandIteration.lean | `SteklovAudit.offBandIterate_increment` | NOT CHECKED (name not found by Lean) |
| Section7OffBandIteration.lean | `SteklovAudit.offBandIterate_error` | NOT CHECKED (name not found by Lean) |
| Section7DyadicPrimitive.lean | `SteklovAudit.quarter_geometric_identity` | NOT CHECKED (name not found by Lean) |
| Section7DyadicPrimitive.lean | `SteklovAudit.quarter_geometric_le` | NOT CHECKED (name not found by Lean) |
| Section7DyadicPrimitive.lean | `SteklovAudit.dyadic_relative_primitive_bound` | NOT CHECKED (name not found by Lean) |
| Section11CountingConventions.lean | `SteklovAudit.realWeylPolynomial_window_increment` | NOT CHECKED (name not found by Lean) |
| Section11CountingConventions.lean | `SteklovAudit.two_term_interval_error_bound` | NOT CHECKED (name not found by Lean) |
| Section7UniformTailObstruction.lean | `SteklovAudit.movingDefect_norm_one` | NOT CHECKED (name not found by Lean) |
| Section7UniformTailObstruction.lean | `SteklovAudit.movingDefect_tail_one` | NOT CHECKED (name not found by Lean) |
| Section7UniformTailObstruction.lean | `SteklovAudit.movingDefect_fixed_tail_zero` | NOT CHECKED (name not found by Lean) |
| Section7UniformTailObstruction.lean | `SteklovAudit.movingDefect_no_uniform_tail` | NOT CHECKED (name not found by Lean) |
| Section7WeightedTail.lean | `SteklovAudit.finite_weighted_tail_bound` | NOT CHECKED (name not found by Lean) |
| Section7WeightedTail.lean | `SteklovAudit.finite_weighted_tail_uniform` | NOT CHECKED (name not found by Lean) |
| Section7OffBandGap.lean | `SteklovAudit.squared_gap_lower_bound` | NOT CHECKED (name not found by Lean) |
| Section7OffBandGap.lean | `SteklovAudit.finite_offband_hs_gap` | NOT CHECKED (name not found by Lean) |
| Section7SpectralDefectIdentity.lean | `SteklovAudit.spectral_defect_entry` | NOT CHECKED (name not found by Lean) |
| Section7SpectralDefectIdentity.lean | `SteklovAudit.spectral_defect_square` | NOT CHECKED (name not found by Lean) |
| Section7SpectralDefectIdentity.lean | `SteklovAudit.finite_sylvester_hs_gap` | NOT CHECKED (name not found by Lean) |
| Section7FrameDefectBudget.lean | `SteklovAudit.window_frame_from_norm_defect` | NOT CHECKED (name not found by Lean) |
| Section7FrameDefectBudget.lean | `SteklovAudit.window_count_from_near_isometry_and_gap` | NOT CHECKED (name not found by Lean) |
| Section7FrameDefectBudget.lean | `SteklovAudit.window_mass_loss_bound` | NOT CHECKED (name not found by Lean) |
| Section7ResolventLocalization.lean | `SteklovAudit.resolvent_intertwining_scalar` | NOT CHECKED (name not found by Lean) |
| Section7ResolventLocalization.lean | `SteklovAudit.resolvent_weighted_partition` | NOT CHECKED (name not found by Lean) |
| Section7ResolventLocalization.lean | `SteklovAudit.resolvent_equal_model` | NOT CHECKED (name not found by Lean) |
| Section9ScaleBudget.lean | `SteklovAudit.constant_scale_error` | NOT CHECKED (name not found by Lean) |
| Section9ScaleBudget.lean | `SteklovAudit.geometric_scale_budget` | NOT CHECKED (name not found by Lean) |
| Section7ResolventTraceObstruction.lean | `SteklovAudit.shifted_resolvent_trace_exact` | NOT CHECKED (name not found by Lean) |
| Section7ResolventTraceObstruction.lean | `SteklovAudit.shifted_resolvent_trace_square` | NOT CHECKED (name not found by Lean) |
| Section7ResolventTraceObstruction.lean | `SteklovAudit.shifted_resolvent_no_uniform_HS_constant` | NOT CHECKED (name not found by Lean) |
| Section11DiscreteHeatObstruction.lean | `SteklovAudit.Section11DiscreteHeatObstruction.multiplicity_positive` | NOT CHECKED (name not found by Lean) |
| Section11DiscreteHeatObstruction.lean | `SteklovAudit.Section11DiscreteHeatObstruction.multiplicity_even` | NOT CHECKED (name not found by Lean) |
| Section11DiscreteHeatObstruction.lean | `SteklovAudit.Section11DiscreteHeatObstruction.multiplicity_odd` | NOT CHECKED (name not found by Lean) |
| Section11DiscreteHeatObstruction.lean | `SteklovAudit.Section11DiscreteHeatObstruction.pair_multiplicity` | NOT CHECKED (name not found by Lean) |
| Section11LaplaceObstruction.lean | `SteklovAudit.Section11LaplaceObstruction.denominator_pos` | NOT CHECKED (name not found by Lean) |
| Section11LaplaceObstruction.lean | `SteklovAudit.Section11LaplaceObstruction.correction_nonneg` | NOT CHECKED (name not found by Lean) |
| Section11LaplaceObstruction.lean | `SteklovAudit.Section11LaplaceObstruction.correction_le_two_t` | NOT CHECKED (name not found by Lean) |
| Section11TwoParameterSqueeze.lean | `SteklovAudit.Section11TwoParameterSqueeze.sharp_error_budget` | NOT CHECKED (name not found by Lean) |
| Section11TwoParameterSqueeze.lean | `SteklovAudit.Section11TwoParameterSqueeze.fixed_width_budget` | NOT CHECKED (name not found by Lean) |
| Section7DuhamelDefectBudget.lean | `SteklovAudit.duhamel_discrete_budget_nonneg` | NOT CHECKED (name not found by Lean) |
| Section7DuhamelDefectBudget.lean | `SteklovAudit.duhamel_discrete_budget_le` | NOT CHECKED (name not found by Lean) |
| Section7DuhamelDefectBudget.lean | `SteklovAudit.scale_error_partial_bound` | NOT CHECKED (name not found by Lean) |
| Section7OverlapMultiplicity.lean | `SteklovAudit.duplicate_rank_overcount` | NOT CHECKED (name not found by Lean) |
| Section7OverlapMultiplicity.lean | `SteklovAudit.duplicate_rank_excess` | NOT CHECKED (name not found by Lean) |
| Section7OverlapMultiplicity.lean | `SteklovAudit.weighted_partition_mass` | NOT CHECKED (name not found by Lean) |
| Section7PartitionFrameBudget.lean | `SteklovAudit.joint_frame_rank_budget` | NOT CHECKED (name not found by Lean) |
| Section7PartitionFrameBudget.lean | `SteklovAudit.joint_frame_no_rank_loss` | NOT CHECKED (name not found by Lean) |
| Section7PartitionFrameBudget.lean | `SteklovAudit.chart_loss_le_total` | NOT CHECKED (name not found by Lean) |
| Section7RankLossThreshold.lean | `SteklovAudit.rank_loss_budget` | NOT CHECKED (name not found by Lean) |
| Section7RankLossThreshold.lean | `SteklovAudit.no_rank_loss_below_threshold` | NOT CHECKED (name not found by Lean) |
| Section7SmoothCutoffHSObstruction.lean | `SteklovAudit.truncated_shift_hs_square` | NOT CHECKED (name not found by Lean) |
| Section7SmoothCutoffHSObstruction.lean | `SteklovAudit.truncated_shift_unbounded` | NOT CHECKED (name not found by Lean) |
| Section7SmoothCutoffHSObstruction.lean | `SteklovAudit.truncated_shift_exceeds` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSandwichBudget.lean | `SteklovAudit.sandwich_mode_count` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSandwichBudget.lean | `SteklovAudit.sandwich_unit_shift_budget` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSandwichBudget.lean | `SteklovAudit.sandwich_no_uniform_budget` | NOT CHECKED (name not found by Lean) |
| Section7SpectralSandwichBudget.lean | `SteklovAudit.sandwich_two_dimensional_count` | NOT CHECKED (name not found by Lean) |
| Section7WeightedPolynomialTrace.lean | `SteklovAudit.weighted_trace_partition` | NOT CHECKED (name not found by Lean) |
| Section7WeightedPolynomialTrace.lean | `SteklovAudit.quadratic_intertwining` | NOT CHECKED (name not found by Lean) |
| Section7WeightedPolynomialTrace.lean | `SteklovAudit.cubic_intertwining` | NOT CHECKED (name not found by Lean) |
| Section7WindowCountBudget.lean | `SteklovAudit.finite_window_mass_budget` | NOT CHECKED (name not found by Lean) |
| Section7WindowCountBudget.lean | `SteklovAudit.finite_window_count_from_gap` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.hs2_nonneg` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.transfer_entry` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.transfer_hs` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.trace_transfer` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.offband_hs` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.window_offband_gap` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.offband_window_bound` | NOT CHECKED (name not found by Lean) |
| AbstractTransfer.lean | `SteklovAudit.AbstractTransfer.trace_transfer_naive` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.cos_time_lipschitz` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.sin_time_lipschitz` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.duhamel_cos_hs` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.duhamel_sin_hs` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.cs_double` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.abs_pair_le_sqrt` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.term_le` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.split_trace_bound` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.cumulative_transfer_bound` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.little_o_of_vanishing_tail` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB.lean | `SteklovAudit.AbstractTransfer.transfer_sharp_law` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB2.lean | `SteklovAudit.AbstractTransfer.norm_cexp_sub_le` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB2.lean | `SteklovAudit.AbstractTransfer.duhamel_entry` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB2.lean | `SteklovAudit.AbstractTransfer.duhamel_entry_sq` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB2.lean | `SteklovAudit.AbstractTransfer.duhamel_hs` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB2.lean | `SteklovAudit.AbstractTransfer.duhamel_hs_of_inputs` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.cumulative_transfer_telescope` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.transfer_gronwall_bound` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.fixed_time_step_budget` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.cumulative_transfer_unbounded` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_diagonal_count` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_shift_energies` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_hs_lower_budget` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_no_uniform_hs_budget` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.inv_add_sq_le_one_add_sq` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.scaled_sq_mul_inv_sq` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.scaled_sq_div_sq` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.div_le_iff_le_scaled` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.indicator_sum_scaled` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.gradient_scaling_cancel` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.gradient_scaling_div` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.scaled_gradient_bound` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.proj_diag_nonneg` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.trace_diagonal_conj` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.weighted_diag_sum_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.trace_proj_cutoff_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.hs2_mul_diag_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.frobenius_sq_mul_diagonal_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.frobenius_mul_diag_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.integral_rpow_two_beta_sub_two` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.integral_rpow_two_mu_sub_one` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.quarter_sq_partial_sum_eq` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.quarter_sq_partial_sum_le` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.tsum_sixteenth_pow_succ` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.tsum_two_pow_neg_four` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.row_sq_le_of_self_test` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.hs2_le_of_pointwise` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.hs_le_of_pointwise` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.geom_partial_le_two_sub` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.geom_partial_le_two` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.collar_geometric_bound` | NOT CHECKED (name not found by Lean) |
| UniformHS71.lean | `SteklovAudit.UniformHS71.collar_geometric_bound_sum` | NOT CHECKED (name not found by Lean) |

## Build errors

```
error: SteklovAudit/AbstractTransferB.lean:77:63: Invalid projection: Type of
  q
is not known; cannot resolve projection `1`
error: SteklovAudit/AbstractTransferB.lean:77:67: Invalid projection: Type of
  q
is not known; cannot resolve projection `2`
error: SteklovAudit/AbstractTransferB.lean:77:84: Invalid projection: Type of
  q
is not known; cannot resolve projection `1`
error: SteklovAudit/AbstractTransferB.lean:77:88: Invalid projection: Type of
  q
is not known; cannot resolve projection `2`
error: build failed
```

## Lean output

```
/home/runner/work/steklov-lean/steklov-lean/AxiomAudit.lean:1:0: error: object file '/home/runner/work/steklov-lean/steklov-lean/.lake/build/lib/lean/SteklovAudit/AbstractTransferB.olean' of module SteklovAudit.AbstractTransferB does not exist

```
