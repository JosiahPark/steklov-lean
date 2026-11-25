# Lean verification status: FAIL

Checked 2026-11-25 03:11 UTC at commit `b7ac3fdba74c`. Last passing commit: `946a68e08497`.

Library declarations checked: 0 of 1382 theorems compile with only Lean's standard axioms.

Ledger inputs proved for the actual operator: 0 of 6. The other inputs are named hypotheses; the two counts are separate.

Scope: these are the algebraic, geometric and limit-assembly lemmas. The main theorem (Theorem 1.3 / 11.1)
is NOT certified: `sharp_integer_law_of_two_scale` and `sharp_real_law_of_two_scale` take the analytic
two-scale bound as a hypothesis, and no Dirichlet-to-Neumann operator is defined in Lean.

Named hypotheses behind the conditional main theorem (`MainConditional.lean`): 6. The goal is to shrink this list.

- H1 splitting: trace linearity of the squared partition.
- H2 area: the area terms add to `|∂T_a| / (4π)`.
- H3 length: the edge length omitted by the vertex cutoffs is `O(ε)`.
- H4 vertex: (7.49).
- H5 edge: (11.3), fed by (7.29), (7.38)/(7.45), (9.1).
- H6 face: Lemma 7.4 with Section 10.2.

Modules audited: 233 files; files declaring theorems but with 0 audited declarations: 232 FOUND
  - SteklovAudit.lean
  - AbstractHSDefect.lean
  - AbstractHSDefectClosed.lean
  - AbstractTransfer.lean
  - AbstractTransferB.lean
  - AbstractTransferB2.lean
  - AbstractTransferB6.lean
  - AffineCutoffTail.lean
  - AffineEigenbasisWitness.lean
  - AffineFullTrace.lean
  - AffineIdentificationNonvacuous.lean
  - AffineParsevalDischarge.lean
  - AffineSpectralPassageFin.lean
  - AffineWitnessFromOperator.lean
  - AsymptoticTransfer.lean
  - CountableCutoffTail.lean
  - Cumulative729Support.lean
  - CumulativeBudget.lean
  - CumulativeBudgetQuantifiers.lean
  - CumulativeBudgetSplit.lean
  - CumulativeTransferAbstract.lean
  - CuspBarrierSupport.lean
  - DihedralBounds.lean
  - DihedralBracket.lean
  - DihedralIntegrable.lean
  - DihedralSanity.lean
  - DihedralThird.lean
  - DuhamelLocalized.lean
  - DuhamelOperatorFin.lean
  - DuhamelSpectral.lean
  - DuhamelWindow.lean
  - EdgeFromModel.lean
  - EdgeLength.lean
  - EdgeMomentum.lean
  - FixedScaleTauberian.lean
  - FixedTimeCumulativeRate.lean
  - FixedWidthCounterexample.lean
  - FixedWidthSmoothing.lean
  - FloorCounterexample.lean
  - Foundations/AffineHarmonic3D.lean
  - Foundations/DiskSteklov.lean
  - Foundations/HalfPlaneDtN.lean
  - Foundations/Trace1D.lean
  - Foundations/TraceHalfLine.lean
  - FourierOneOverT.lean
  - FullTraceSmallSeparate.lean
  - GridLaw.lean
  - GrowthInputsWitness.lean
  - H5ColCount.lean
  - H5ColCountAudit.lean
  - H5ColMassSplit.lean
  - H5ColNorm.lean
  - H5ColNormEv.lean
  - H5ColNormEvAudit.lean
  - H5Compare.lean
  - H5Completeness.lean
  - H5CountAudit.lean
  - H5CountRows.lean
  - H5CutoffAffineInstance.lean
  - H5CutoffInterface.lean
  - H5CutoffObstruction.lean
  - H5CutoffRatioSufficient.lean
  - H5CutoffSides.lean
  - H5CutoffSmoothed.lean
  - H5CutoffSplitTerminal.lean
  - H5CutoffTerminal.lean
  - H5CutoffTerminalIff.lean
  - H5CutoffWeakRows.lean
  - H5DeltaVanishNeeded.lean
  - H5DiffAudit.lean
  - H5DiffCount.lean
  - H5DiffHighAudit.lean
  - H5DiffHighMass.lean
  - H5EvGrowWitness.lean
  - H5EvLowCountIndep.lean
  - H5EvPaperScale.lean
  - H5EvPaperScaleAudit.lean
  - H5EventualAudit.lean
  - H5EventualRows.lean
  - H5EventualTarget.lean
  - H5GlobalLip.lean
  - H5GlobalLipAudit.lean
  - H5GlobalLipRows.lean
  - H5GlobalLipRowsAudit.lean
  - H5GlobalLipRowsEv.lean
  - H5GlobalLipRowsEvAudit.lean
  - H5GlobalLipRowsEvStrict.lean
  - H5GlobalLipRowsPow.lean
  - H5GlobalLipRowsPowAudit.lean
  - H5GlobalLipRowsPowStrict.lean
  - H5GlobalLipRowsStrict.lean
  - H5GlobalLipStrict.lean
  - H5GlobalVanishNeeded.lean
  - H5HiLinear.lean
  - H5HiLinearAudit.lean
  - H5HiLinearStrict.lean
  - H5HighMass2Audit.lean
  - H5HighMassAudit.lean
  - H5Joint.lean
  - H5JointAudit.lean
  - H5JointCutoffNeeded.lean
  - H5JointIff.lean
  - H5JointSel.lean
  - H5JointSelAudit.lean
  - H5JointSelIff.lean
  - H5JointStrict.lean
  - H5LipRows.lean
  - H5LowCount.lean
  - H5LowCountGrowth.lean
  - H5LowLinear.lean
  - H5LowLinearAudit.lean
  - H5LowLinearRows.lean
  - H5LowLinearStrict.lean
  - H5LowMass.lean
  - H5MaskSplit.lean
  - H5MassAudit.lean
  - H5MassEvNeeded.lean
  - H5MassRow.lean
  - H5MassSplit.lean
  - H5MissingMass.lean
  - H5PaperAudit.lean
  - H5PaperRows.lean
  - H5Parseval.lean
  - H5PinnedCutoffIsTarget.lean
  - H5PinnedCutoffVanish.lean
  - H5PinnedDataRows.lean
  - H5PinnedNonvacuous.lean
  - H5PinnedNotTarget.lean
  - H5PinnedPtsLip.lean
  - H5PinnedPtsLipStrict.lean
  - H5PinnedRows.lean
  - H5PinnedRowsPow.lean
  - H5PinnedRowsPowStrict.lean
  - H5PinnedSumSmall.lean
  - H5PinnedZeroAudit.lean
  - H5Reindex.lean
  - H5RowNormEv.lean
  - H5RowNormEvAudit.lean
  - H5RowNormWitness.lean
  - H5SelDirect.lean
  - H5SelDirectAudit.lean
  - H5SelDirectIff.lean
  - H5SelMin.lean
  - H5SelMinStrict.lean
  - H5SideAudit.lean
  - H5SideRows.lean
  - H5SmoothedAudit.lean
  - H5SmoothedColAudit.lean
  - H5SmoothedHigh.lean
  - H5SmoothedIdent.lean
  - H5SmoothedWitness.lean
  - H5Split.lean
  - H5TailAudit.lean
  - H5TailEv.lean
  - H5TailEvAudit.lean
  - H5TailEvStrict.lean
  - H5TailRate.lean
  - H5WeakAudit.lean
  - H5WeakRows.lean
  - H5WindowProfile.lean
  - H5WindowWitness.lean
  - H5bQuantifierOrder.lean
  - HSBasisIndependence.lean
  - HSBasisIndependenceReal.lean
  - HSNoTrace.lean
  - HeatFiber.lean
  - IdentificationBudget.lean
  - IdentificationBudgetData.lean
  - LeakageLayerCake.lean
  - LedgerNonvacuousC6.lean
  - LedgerNonvacuousD5.lean
  - MainConditional.lean
  - ModelEdgeLawGammaFamily.lean
  - ModelEdgeLawGammaFree.lean
  - ModelEdgeLawReduction.lean
  - ModelEdgeLawSixEdges.lean
  - MultiChartTrace.lean
  - PartitionTrace.lean
  - PowerShiftTransfer.lean
  - PropagatorTrace.lean
  - RealToIntegerLaw.lean
  - ResidualLink.lean
  - ReviewCandidates.lean
  - ReviewExtensions.lean
  - RieszCounterexample.lean
  - RieszMeans.lean
  - RightAngleCalibration.lean
  - RpowScale.lean
  - ScalingLaw.lean
  - Section11AllFixedScales.lean
  - Section11ApproximateFixedScales.lean
  - Section11FiniteScaleBracket.lean
  - Section11ShiftBudgetOptimization.lean
  - Section11ShiftedModelSqueeze.lean
  - Section11ShrinkingSmoothing.lean
  - Section11SmoothingCounterexample.lean
  - Section11ThresholdInstability.lean
  - Section11WindowFromSmoothing.lean
  - Section4Scalar.lean
  - Section7CumulativeTransfer.lean
  - Section7FixedWindowHSObstruction.lean
  - Section7IdentificationTraceBudget.lean
  - Section7LipschitzHSTransfer.lean
  - Section7OneSidedCountingTransfer.lean
  - Section7RankLeakage.lean
  - Section7TraceRankAmplification.lean
  - Section7WeightedLeakage.lean
  - Section9NearResonanceObstruction.lean
  - Section9SpectralGapLeakage.lean
  - SectorTrace.lean
  - SharpLawTransfer.lean
  - SharpLawUnique.lean
  - SpectralCounting.lean
  - TaylorRemainder.lean
  - TetraAffineFlux.lean
  - TetraAssemblyFace.lean
  - TetraEdgeLawNonvacuous.lean
  - TetraEdgeLawOverlap.lean
  - TraceLocalMass.lean
  - TraceLocalMassGrowth.lean
  - TraceNormBudget.lean
  - TriangleQuadrature.lean
  - TwoParameterSmoothing.lean
  - UniformHS71.lean
  - VertexLog.lean
  - WedgeChannel.lean
  - WeightedToUnweighted.lean
  - WeightedToUnweightedNonvacuous.lean
  - WindowBoundedNonvacuous.lean
  - WindowBounds.lean
  - WindowDefectFullTrace.lean
  - WindowLocalMassBounded.lean

Escape hatches (sorry, admit, axiom, maxHeartbeats, native_decide, unsafe, opaque): none

Tautologies (proof is one of the theorem's own hypotheses): none

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
| AbstractHSDefect.lean | `SteklovAudit.AbstractHSDefect.localized_hs_defect_bound` | NOT CHECKED (name not found by Lean) |
| AbstractHSDefectClosed.lean | `SteklovAudit.AbstractHSDefectClosed.projFrobeniusContraction_of_projection` | NOT CHECKED (name not found by Lean) |
| AbstractHSDefectClosed.lean | `SteklovAudit.AbstractHSDefectClosed.localized_hs_defect_bound_of_projection` | NOT CHECKED (name not found by Lean) |
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
| AbstractTransferB6.lean | `SteklovAudit.AbstractTransfer.offband_entry_mul` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB6.lean | `SteklovAudit.AbstractTransfer.offband_window_mass` | NOT CHECKED (name not found by Lean) |
| AbstractTransferB6.lean | `SteklovAudit.AbstractTransfer.window_count_band` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.tPar_pos` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.muAff_pos` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.tPar_sq` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.affine_two_over_t_sq` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.affine_mu_eq` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.residual_pairing_phi` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.affine_residual_sum` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.muVec_le` | NOT CHECKED (name not found by Lean) |
| AffineCutoffTail.lean | `SteklovAudit.AffineCutoffTail.affine_cutoff_tail` | NOT CHECKED (name not found by Lean) |
| AffineEigenbasisWitness.lean | `SteklovAudit.AffineEigenbasisWitness.parseval_of_witness` | NOT CHECKED (name not found by Lean) |
| AffineEigenbasisWitness.lean | `SteklovAudit.AffineEigenbasisWitness.cutoff_of_witness` | NOT CHECKED (name not found by Lean) |
| AffineFullTrace.lean | `SteklovAudit.AffineFullTrace.first_moment` | NOT CHECKED (name not found by Lean) |
| AffineFullTrace.lean | `SteklovAudit.AffineFullTrace.weighted_first_moment` | NOT CHECKED (name not found by Lean) |
| AffineFullTrace.lean | `SteklovAudit.AffineFullTrace.affine_full_trace_le` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.blockT_apply` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.blockT_symm` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.rRes_sq` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.fin4_cases` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.e_inner_self` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.blockT_e0` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.block_residual` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.block_residual_norm` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.block_residual_inner` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.identification_of_block` | NOT CHECKED (name not found by Lean) |
| AffineIdentificationNonvacuous.lean | `SteklovAudit.AffineIdentificationNonvacuous.exists_identification` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.mass_phi0` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.mass_phi1` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.mass_phi2` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.mass_phi3` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.mass_sum` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.energy_sum` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.residualOrth_of_identification` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.parseval_discharged` | NOT CHECKED (name not found by Lean) |
| AffineParsevalDischarge.lean | `SteklovAudit.AffineParsevalDischarge.full_trace_discharged` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.preOfSymmetric_lam` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.preOfSymmetric_A_apply` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.preOfSymmetric_u` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.preOfSymmetric_b` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.full_trace_fin` | NOT CHECKED (name not found by Lean) |
| AffineSpectralPassageFin.lean | `SteklovAudit.AffineSpectralPassageFin.full_trace_fin_sum` | NOT CHECKED (name not found by Lean) |
| AffineWitnessFromOperator.lean | `SteklovAudit.AffineWitnessFromOperator.sums_of_data` | NOT CHECKED (name not found by Lean) |
| AffineWitnessFromOperator.lean | `SteklovAudit.AffineWitnessFromOperator.witnessOfOperator_lam` | NOT CHECKED (name not found by Lean) |
| AffineWitnessFromOperator.lean | `SteklovAudit.AffineWitnessFromOperator.witnessOfOperator_J` | NOT CHECKED (name not found by Lean) |
| AffineWitnessFromOperator.lean | `SteklovAudit.AffineWitnessFromOperator.parseval_of_operator` | NOT CHECKED (name not found by Lean) |
| AffineWitnessFromOperator.lean | `SteklovAudit.AffineWitnessFromOperator.cutoff_of_operator` | NOT CHECKED (name not found by Lean) |
| AsymptoticTransfer.lean | `SteklovAudit.AsymptoticTransfer.law_of_shifted_bounds` | NOT CHECKED (name not found by Lean) |
| AsymptoticTransfer.lean | `SteklovAudit.AsymptoticTransfer.rpow_little_o` | NOT CHECKED (name not found by Lean) |
| AsymptoticTransfer.lean | `SteklovAudit.AsymptoticTransfer.rpow_neg_small` | NOT CHECKED (name not found by Lean) |
| AsymptoticTransfer.lean | `SteklovAudit.AsymptoticTransfer.defect_over_shift` | NOT CHECKED (name not found by Lean) |
| AsymptoticTransfer.lean | `SteklovAudit.AsymptoticTransfer.asymptotic_transfer` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.mass_nonneg` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.moment_nonneg` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.M_nonneg` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.E_nonneg` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_mass` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.tsum_mass_le` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_moment` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.tsum_moment_le` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.abs_le_half_one_add_sq` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.bound_nonneg` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_bound` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.centered_abs_le` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_of_abs_le` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_centered` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_le_part` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.summable_gt_part` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.S_sub_Sle` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.tail_term_le` | NOT CHECKED (name not found by Lean) |
| CountableCutoffTail.lean | `SteklovAudit.CountableCutoffTail.Cert.cutoff_tail_le` | NOT CHECKED (name not found by Lean) |
| Cumulative729Support.lean | `SteklovAudit.Cumulative729Support.log_plus_vanishing_is_o_L` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.uniform_defect_is_O` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.tail_eta_form` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.tail_littleO_of_cutoff_bound` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.tail_over_M_is_o` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.order_of_limits_matters` | NOT CHECKED (name not found by Lean) |
| CumulativeBudget.lean | `SteklovAudit.CumulativeBudget.time_factor_preserves_o` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_approx` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.approx_of_littleO` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.approx_iff` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_split_rate` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_split_nat` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_window_defect` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.littleO_of_window_defect'` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetQuantifiers.lean | `SteklovAudit.CumulativeBudgetQuantifiers.window_needs_vanishing` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetSplit.lean | `SteklovAudit.CumulativeBudgetSplit.littleO_of_split` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetSplit.lean | `SteklovAudit.CumulativeBudgetSplit.littleO_of_split'` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetSplit.lean | `SteklovAudit.CumulativeBudgetSplit.split_of_cutoff_bound` | NOT CHECKED (name not found by Lean) |
| CumulativeBudgetSplit.lean | `SteklovAudit.CumulativeBudgetSplit.split_needs_uniform_C` | NOT CHECKED (name not found by Lean) |
| CumulativeTransferAbstract.lean | `SteklovAudit.CumulativeTransferAbstract.time_factor_cancellation` | NOT CHECKED (name not found by Lean) |
| CumulativeTransferAbstract.lean | `SteklovAudit.CumulativeTransferAbstract.duhamel_time_controlled` | NOT CHECKED (name not found by Lean) |
| CumulativeTransferAbstract.lean | `SteklovAudit.CumulativeTransferAbstract.vanishing_tail_gives_oL` | NOT CHECKED (name not found by Lean) |
| CuspBarrierSupport.lean | `SteklovAudit.CuspBarrierSupport.transverse_coeff_neg` | NOT CHECKED (name not found by Lean) |
| CuspBarrierSupport.lean | `SteklovAudit.CuspBarrierSupport.longitudinal_subordinate` | NOT CHECKED (name not found by Lean) |
| CuspBarrierSupport.lean | `SteklovAudit.CuspBarrierSupport.admissible_exponents_nonempty` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.ioi_integral_exp_neg_mul` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.dihedralCoeff_le` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.dihedralCoeff_tetra_le` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.integrand_antitone` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.dihedralCoeff_antitone` | NOT CHECKED (name not found by Lean) |
| DihedralBounds.lean | `SteklovAudit.DihedralBounds.dihedralCoeff_tetra_ge` | NOT CHECKED (name not found by Lean) |
| DihedralBracket.lean | `SteklovAudit.DihedralBracket.pi_div_three_lt_tetraAngle` | NOT CHECKED (name not found by Lean) |
| DihedralBracket.lean | `SteklovAudit.DihedralBracket.bound_le_of_ge` | NOT CHECKED (name not found by Lean) |
| DihedralBracket.lean | `SteklovAudit.DihedralBracket.dihedralCoeff_tetra_le_bracket` | NOT CHECKED (name not found by Lean) |
| DihedralBracket.lean | `SteklovAudit.DihedralBracket.dihedralCoeff_tetra_bracket` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.sinh_le_mul_exp` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.half_le_sinh` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.exp_half_le_cosh` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.integrand_bound` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.integrableOn_integrand` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.integrableOn_dihedral` | NOT CHECKED (name not found by Lean) |
| DihedralIntegrable.lean | `SteklovAudit.DihedralIntegrable.integrableOn_dihedral_tetra` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.dihedralCoeff_pi` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.integrand_pos` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.dihedralCoeff_pos` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.cos_tetraAngle` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.tetraAngle_lt_pi_div_two` | NOT CHECKED (name not found by Lean) |
| DihedralSanity.lean | `SteklovAudit.DihedralSanity.dihedralCoeff_tetra_pos` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.integrand_third` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.hasDerivAt_G` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.GThird_zero` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.tendsto_G` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.integral_third` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.dihedralCoeff_pi_div_three` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.dihedralCoeff_tetra_le_third` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.dihedralCoeff_tetra_bracket_third` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.upper_num` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.lower_num` | NOT CHECKED (name not found by Lean) |
| DihedralThird.lean | `SteklovAudit.DihedralThird.dihedralCoeff_tetra_decimal` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.conj_diag_mul` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.diagonal_mul_comm` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.conj_diag_comm` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.prop_comm_Z` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.op_comm_Z` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.localized_eq` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.duhamel_localized_sq` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.duhamel_localized_le` | NOT CHECKED (name not found by Lean) |
| DuhamelLocalized.lean | `SteklovAudit.DuhamelLocalized.defectSmall_zero` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.conj_comm_coords` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.defect_coords` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.prop_coords` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.hsSq_ct_left` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.hsSq_coords` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.hsSq_of_mul` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.norm_ofReal_sub_sq` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.duhamel_hs_matrix` | NOT CHECKED (name not found by Lean) |
| DuhamelOperatorFin.lean | `SteklovAudit.DuhamelOperatorFin.duhamel_hs_matrix_zero` | NOT CHECKED (name not found by Lean) |
| DuhamelSpectral.lean | `SteklovAudit.DuhamelSpectral.exp_sub_one_le` | NOT CHECKED (name not found by Lean) |
| DuhamelSpectral.lean | `SteklovAudit.DuhamelSpectral.duhamel_entry_le` | NOT CHECKED (name not found by Lean) |
| DuhamelSpectral.lean | `SteklovAudit.DuhamelSpectral.duhamel_hs_le` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDiff_nonneg` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDefect_nonneg` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDiff_le` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.window_hsDiff_le` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDiff_zero` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDiff_eq_zero_of_defect` | NOT CHECKED (name not found by Lean) |
| DuhamelWindow.lean | `SteklovAudit.DuhamelWindow.hsDefect_example` | NOT CHECKED (name not found by Lean) |
| EdgeFromModel.lean | `SteklovAudit.EdgeFromModel.edge_of_model_compare` | NOT CHECKED (name not found by Lean) |
| EdgeFromModel.lean | `SteklovAudit.EdgeFromModel.theorem_11_1_of_C4` | NOT CHECKED (name not found by Lean) |
| EdgeFromModel.lean | `SteklovAudit.EdgeFromModel.formula_11_4_of_C4` | NOT CHECKED (name not found by Lean) |
| EdgeFromModel.lean | `SteklovAudit.EdgeFromModel.nonvacuous_C4` | NOT CHECKED (name not found by Lean) |
| EdgeLength.lean | `SteklovAudit.EdgeLength.edge_integral_bounds` | NOT CHECKED (name not found by Lean) |
| EdgeLength.lean | `SteklovAudit.EdgeLength.six_edge_length` | NOT CHECKED (name not found by Lean) |
| EdgeLength.lean | `SteklovAudit.EdgeLength.length_bound` | NOT CHECKED (name not found by Lean) |
| EdgeLength.lean | `SteklovAudit.EdgeLength.theorem_11_1_of_C6` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.zero_beyond` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.neg_moment_deriv` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.deriv_test` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.inner_k` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.inner_k_abs` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.kernel_integrable` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.edge_momentum` | NOT CHECKED (name not found by Lean) |
| EdgeMomentum.lean | `SteklovAudit.EdgeMomentum.formula_3_13` | NOT CHECKED (name not found by Lean) |
| FixedScaleTauberian.lean | `SteklovAudit.FixedScaleTauberian.smooth_sandwich` | NOT CHECKED (name not found by Lean) |
| FixedScaleTauberian.lean | `SteklovAudit.FixedScaleTauberian.sharp_law_of_shrinking_scales` | NOT CHECKED (name not found by Lean) |
| FixedScaleTauberian.lean | `SteklovAudit.FixedScaleTauberian.sharp_law_of_finite_kernels` | NOT CHECKED (name not found by Lean) |
| FixedTimeCumulativeRate.lean | `SteklovAudit.FixedTimeCumulativeRate.log_plus_power_vanishing_is_power_saving` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.sin_quarter` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.sin_three_quarter` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.N_quarter_lower` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.N_three_quarter_upper` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.not_sharp_law` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.hasDerivAt_F` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.deriv_F_pos` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.F_strictMonoOn` | NOT CHECKED (name not found by Lean) |
| FixedWidthCounterexample.lean | `SteklovAudit.FixedWidthCounterexample.N_monotoneOn` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.smooth_eq` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.F_pair` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.smooth_close` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.smoothed_sharp_law` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.Nc_eq` | NOT CHECKED (name not found by Lean) |
| FixedWidthSmoothing.lean | `SteklovAudit.FixedWidthSmoothing.fixed_width_insufficient` | NOT CHECKED (name not found by Lean) |
| FloorCounterexample.lean | `SteklovAudit.FloorCounterexample.sin_quarter` | NOT CHECKED (name not found by Lean) |
| FloorCounterexample.lean | `SteklovAudit.FloorCounterexample.floor_excess` | NOT CHECKED (name not found by Lean) |
| FloorCounterexample.lean | `SteklovAudit.FloorCounterexample.not_sharp` | NOT CHECKED (name not found by Lean) |
| FloorCounterexample.lean | `SteklovAudit.FloorCounterexample.hasDerivAt_F` | NOT CHECKED (name not found by Lean) |
| FloorCounterexample.lean | `SteklovAudit.FloorCounterexample.deriv_F_pos` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.hasDerivAt_u_x` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.hasDerivAt_u_y` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.hasDerivAt_u_z` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.second_partials_zero` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.laplacian_zero` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.normal_derivative_at` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.normal_derivative` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.face_normal_derivative` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.face_flux_values` | NOT CHECKED (name not found by Lean) |
| Foundations/AffineHarmonic3D.lean | `SteklovAudit.Foundations.AffineHarmonic3D.face_flux_sum_zero` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.lap_core` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_u_r` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_u_rr` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_u_θ` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_u_θθ` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.laplacian_polar_u` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_v_r` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_v_rr` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_v_θ` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.hasDerivAt_v_θθ` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.laplacian_polar_v` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.steklov_u` | NOT CHECKED (name not found by Lean) |
| Foundations/DiskSteklov.lean | `SteklovAudit.Foundations.DiskSteklov.steklov_v` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.hasDerivAt_u_x` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.hasDerivAt_u_xx` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.hasDerivAt_u_y` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.hasDerivAt_u_yy` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.laplacian_u` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.dtn_symbol` | NOT CHECKED (name not found by Lean) |
| Foundations/HalfPlaneDtN.lean | `SteklovAudit.Foundations.HalfPlaneDtN.tendsto_u_atTop` | NOT CHECKED (name not found by Lean) |
| Foundations/Trace1D.lean | `SteklovAudit.Foundations.Trace1D.pointwise_bound` | NOT CHECKED (name not found by Lean) |
| Foundations/Trace1D.lean | `SteklovAudit.Foundations.Trace1D.trace_1d` | NOT CHECKED (name not found by Lean) |
| Foundations/TraceHalfLine.lean | `SteklovAudit.Foundations.TraceHalfLine.cross_abs_le` | NOT CHECKED (name not found by Lean) |
| Foundations/TraceHalfLine.lean | `SteklovAudit.Foundations.TraceHalfLine.trace_halfLine` | NOT CHECKED (name not found by Lean) |
| FourierOneOverT.lean | `SteklovAudit.FourierOneOverT.eps_nonneg_of_bound` | NOT CHECKED (name not found by Lean) |
| FourierOneOverT.lean | `SteklovAudit.FourierOneOverT.fourier_cancel_le` | NOT CHECKED (name not found by Lean) |
| FourierOneOverT.lean | `SteklovAudit.FourierOneOverT.inv_weight_ok` | NOT CHECKED (name not found by Lean) |
| FourierOneOverT.lean | `SteklovAudit.FourierOneOverT.fourier_cancel_inv` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.S_zero` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.fullTraceSmall_zero` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.ratio_small` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.not_littleO_idD` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.traceMatches_fails` | NOT CHECKED (name not found by Lean) |
| FullTraceSmallSeparate.lean | `SteklovAudit.FullTraceSmallSeparate.fullTraceSmall_not_target` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.stepN_monotone` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.stepN_nat` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.stepN_half` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.step_integer_law` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.step_not_real_law` | NOT CHECKED (name not found by Lean) |
| GridLaw.lean | `SteklovAudit.GridLaw.real_law_of_fine_grids` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.growth_hJ_forces_Mloc_zero` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.growth_hJ_forces_J_zero` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.growth_trace_zero` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.trace_littleO_of_growth_pos` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.hs2_fin1` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_K_hs2` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_J_hs2` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_eps_sq` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_eps_nonneg` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_rate` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_trace_eq_one` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.growth_inputs_nonvacuous` | NOT CHECKED (name not found by Lean) |
| GrowthInputsWitness.lean | `SteklovAudit.GrowthInputsWitness.witness_littleO` | NOT CHECKED (name not found by Lean) |
| H5ColCount.lean | `SteklovAudit.H5ColCount.colMass_eq_of_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5ColCount.lean | `SteklovAudit.H5ColCount.rowMass_eq_of_colNorm` | NOT CHECKED (name not found by Lean) |
| H5ColCount.lean | `SteklovAudit.H5ColCount.rowNorm_colMiss` | NOT CHECKED (name not found by Lean) |
| H5ColCount.lean | `SteklovAudit.H5ColCount.h5b_of_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5ColCountAudit.lean | `SteklovAudit.H5ColCountAudit.colMiss_iff_cardGap` | NOT CHECKED (name not found by Lean) |
| H5ColCountAudit.lean | `SteklovAudit.H5ColCountAudit.smCol_cardGap` | NOT CHECKED (name not found by Lean) |
| H5ColCountAudit.lean | `SteklovAudit.H5ColCountAudit.rowNormOfNorm_m2` | NOT CHECKED (name not found by Lean) |
| H5ColCountAudit.lean | `SteklovAudit.H5ColCountAudit.rowNormOfNorm_target` | NOT CHECKED (name not found by Lean) |
| H5ColMassSplit.lean | `SteklovAudit.H5ColMassSplit.col_missing_split` | NOT CHECKED (name not found by Lean) |
| H5ColMassSplit.lean | `SteklovAudit.H5ColMassSplit.h5b_of_high_mass2` | NOT CHECKED (name not found by Lean) |
| H5ColNorm.lean | `SteklovAudit.H5ColNorm.colNorm_rowMiss` | NOT CHECKED (name not found by Lean) |
| H5ColNorm.lean | `SteklovAudit.H5ColNorm.h5b_of_colNorm` | NOT CHECKED (name not found by Lean) |
| H5ColNorm.lean | `SteklovAudit.H5ColNorm.smoothedOfColNorm_m2` | NOT CHECKED (name not found by Lean) |
| H5ColNormEv.lean | `SteklovAudit.H5ColNormEv.colNormEv_rowMiss` | NOT CHECKED (name not found by Lean) |
| H5ColNormEv.lean | `SteklovAudit.H5ColNormEv.toSmoothedEv_nB` | NOT CHECKED (name not found by Lean) |
| H5ColNormEv.lean | `SteklovAudit.H5ColNormEv.h5b_of_colNormEv` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_colNorm` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_bessel` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_K` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_defect` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_tail` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_count` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.cnD_lowCount` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.colNormEvWitness_genuine` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.colNorm_count_neg_one` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.colNormEv_not_colNorm` | NOT CHECKED (name not found by Lean) |
| H5ColNormEvAudit.lean | `SteklovAudit.H5ColNormEvAudit.colNormEvWitness_target` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.compare_is_target` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.hs2_mask_le` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.h5b_of_inputs` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.inputs_iff_target` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.inputs_nonempty` | NOT CHECKED (name not found by Lean) |
| H5Compare.lean | `SteklovAudit.H5Compare.theorem_11_1_of_F` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.weighted_sum_split` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.defect_abs_le` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.side_of_count_and_defect` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.defect_le_sup` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.side_of_count_and_sup` | NOT CHECKED (name not found by Lean) |
| H5Completeness.lean | `SteklovAudit.H5Completeness.side_of_count_and_defect_nonvacuous` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_trueCount` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_modelCount` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_rowDefect` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_colDefect` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_colBessel` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_bessel` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_count` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_defect` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_tail` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.z_lowCount` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.countWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.true_count_not_target` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.model_count_not_target` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.defect_rows_not_target` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.const_sum_fin` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.ceil_trueCount` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.ceil_rowTrace` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.ceil_trueSide_fails` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.trueCount_not_trueSide` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.rowDefect_of_sup` | NOT CHECKED (name not found by Lean) |
| H5CountAudit.lean | `SteklovAudit.H5CountAudit.rowDefect_arctan` | NOT CHECKED (name not found by Lean) |
| H5CountRows.lean | `SteklovAudit.H5CountRows.toSides_d1` | NOT CHECKED (name not found by Lean) |
| H5CountRows.lean | `SteklovAudit.H5CountRows.toSides_d2` | NOT CHECKED (name not found by Lean) |
| H5CountRows.lean | `SteklovAudit.H5CountRows.h5b_of_counts` | NOT CHECKED (name not found by Lean) |
| H5CutoffAffineInstance.lean | `SteklovAudit.H5CutoffAffineInstance.affine_ratio_eq` | NOT CHECKED (name not found by Lean) |
| H5CutoffAffineInstance.lean | `SteklovAudit.H5CutoffAffineInstance.affine_ratio_O_inv` | NOT CHECKED (name not found by Lean) |
| H5CutoffAffineInstance.lean | `SteklovAudit.H5CutoffAffineInstance.affine_ratioLittleO` | NOT CHECKED (name not found by Lean) |
| H5CutoffInterface.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.cutoff_error_le` | NOT CHECKED (name not found by Lean) |
| H5CutoffInterface.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.full_trace_matches` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.cos_even` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.cos_odd` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.cos_even_succ` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.block_mass` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.block_defect` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.block_first_moment` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.block_centered` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_sum` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_defect_sum` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_below_cutoff` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_ratio_le` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_ratio_small` | NOT CHECKED (name not found by Lean) |
| H5CutoffObstruction.lean | `SteklovAudit.H5CutoffObstruction.obstruction_D_ratio` | NOT CHECKED (name not found by Lean) |
| H5CutoffRatioSufficient.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.ratio_le_of_gap` | NOT CHECKED (name not found by Lean) |
| H5CutoffRatioSufficient.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.ratioLittleO_of_gap_energy` | NOT CHECKED (name not found by Lean) |
| H5CutoffSides.lean | `SteklovAudit.H5CutoffSides.double_sum_split` | NOT CHECKED (name not found by Lean) |
| H5CutoffSides.lean | `SteklovAudit.H5CutoffSides.cutoff_of_sides` | NOT CHECKED (name not found by Lean) |
| H5CutoffSides.lean | `SteklovAudit.H5CutoffSides.discVanish_of_sides` | NOT CHECKED (name not found by Lean) |
| H5CutoffSmoothed.lean | `SteklovAudit.H5CutoffSmoothed.target_of_cutoffRowδ` | NOT CHECKED (name not found by Lean) |
| H5CutoffSmoothed.lean | `SteklovAudit.H5CutoffSmoothed.cutoffRowδ_iff_target` | NOT CHECKED (name not found by Lean) |
| H5CutoffSplitTerminal.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.fullTraceSmall_of_split` | NOT CHECKED (name not found by Lean) |
| H5CutoffSplitTerminal.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.h5_of_cutoff_split` | NOT CHECKED (name not found by Lean) |
| H5CutoffSplitTerminal.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.fullTraceSplit_of_small` | NOT CHECKED (name not found by Lean) |
| H5CutoffSplitTerminal.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.fullTraceSplit_iff` | NOT CHECKED (name not found by Lean) |
| H5CutoffTerminal.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.h5_of_cutoff_route` | NOT CHECKED (name not found by Lean) |
| H5CutoffTerminalIff.lean | `SteklovAudit.H5CutoffTerminalIff.fullTraceSmall_of_h5` | NOT CHECKED (name not found by Lean) |
| H5CutoffTerminalIff.lean | `SteklovAudit.H5CutoffTerminalIff.h5_iff_fullTraceSmall` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.h5_of_weak_rows` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.gapLinear_zeroFamily` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.energySmall_zeroFamily` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.windowTraceBound_zeroFamily` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.weak_rows_zeroFamily` | NOT CHECKED (name not found by Lean) |
| H5CutoffWeakRows.lean | `SteklovAudit.H5CutoffWeakRows.weak_rows_need_traceMatches` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_massLin` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_defectLin` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_prod` | NOT CHECKED (name not found by Lean) |
| H5DeltaVanishNeeded.lean | `SteklovAudit.H5DeltaVanishNeeded.linD_not_vanish` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.z_diffCount` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.self_diff_bound` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.diffWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.double_diffCount` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.double_trueCount_fails` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.diff_not_counts` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.ceil_diffCount` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.ceil_not_target` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.diff_row_not_target` | NOT CHECKED (name not found by Lean) |
| H5DiffAudit.lean | `SteklovAudit.H5DiffAudit.diff_rows_E_free` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.diff_of_counts` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.defect_abs_le_mass` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.cutoff_of_diff_count` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.cutoff_of_diff_count_nonvacuous` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.h5b_of_diff` | NOT CHECKED (name not found by Lean) |
| H5DiffCount.lean | `SteklovAudit.H5DiffCount.toPaper_disc` | NOT CHECKED (name not found by Lean) |
| H5DiffHighAudit.lean | `SteklovAudit.H5DiffHighAudit.diffHigh2Witness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5DiffHighAudit.lean | `SteklovAudit.H5DiffHighAudit.highMass2_double_empty_fails` | NOT CHECKED (name not found by Lean) |
| H5DiffHighAudit.lean | `SteklovAudit.H5DiffHighAudit.diffHigh2_not_highMass2` | NOT CHECKED (name not found by Lean) |
| H5DiffHighMass.lean | `SteklovAudit.H5DiffHighMass.vanish_of_split` | NOT CHECKED (name not found by Lean) |
| H5DiffHighMass.lean | `SteklovAudit.H5DiffHighMass.h5b_of_diffHigh2` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_colNorm` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_K` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_rowMiss` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_colMiss` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_count` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growD_lowCount` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growWitness_unbounded` | NOT CHECKED (name not found by Lean) |
| H5EvGrowWitness.lean | `SteklovAudit.H5EvGrowWitness.growWitness_target` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_colNorm` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_K` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_count` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_ha` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_hb` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_filter_univ` | NOT CHECKED (name not found by Lean) |
| H5EvLowCountIndep.lean | `SteklovAudit.H5EvLowCountIndep.flatD_not_lowCount` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScale.lean | `SteklovAudit.H5EvPaperScale.sq_le_one_add_sq` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScale.lean | `SteklovAudit.H5EvPaperScale.paperScale_count` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScale.lean | `SteklovAudit.H5EvPaperScale.paperScale_defect` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScale.lean | `SteklovAudit.H5EvPaperScale.toSmoothedEv_nA` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScale.lean | `SteklovAudit.H5EvPaperScale.h5b_of_paperScale` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.one_add_sq_le_four_sq` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.smoothedEv_count_paper` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.smoothedEv_defect_paper` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.ofSmoothedEv_nA` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.ofSmoothedEv_Cm` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.ofSmoothedEv_Ck` | NOT CHECKED (name not found by Lean) |
| H5EvPaperScaleAudit.lean | `SteklovAudit.H5EvPaperScaleAudit.ofSmoothedEv_target` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.smoothed_count_neg_one` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_rowSq` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_colSq` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_K` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_count` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_defect` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_tail` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evOneD_lowCount` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evWitness_not_smoothed` | NOT CHECKED (name not found by Lean) |
| H5EventualAudit.lean | `SteklovAudit.H5EventualAudit.evWitness_target` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.evN_pos` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.evNB_pos` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.evN_neg` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.evNB_neg` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.evD_pos` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.tau_nonneg` | NOT CHECKED (name not found by Lean) |
| H5EventualRows.lean | `SteklovAudit.H5EventualRows.c_nonneg` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.evM1_pos` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.evM1_neg` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.evM2_pos` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.evM2_neg` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.evD_neg` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.hs2_fin0` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.card_filter_zData` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.ev_Esm_eq` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.ev_Emodsm_eq` | NOT CHECKED (name not found by Lean) |
| H5EventualTarget.lean | `SteklovAudit.H5EventualTarget.h5b_of_smoothedEv` | NOT CHECKED (name not found by Lean) |
| H5GlobalLip.lean | `SteklovAudit.H5GlobalLip.toSelMin_Λ0` | NOT CHECKED (name not found by Lean) |
| H5GlobalLip.lean | `SteklovAudit.H5GlobalLip.h5b_of_globalLipInputs` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipAudit.lean | `SteklovAudit.H5GlobalLipAudit.ofTarget_Λ` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipAudit.lean | `SteklovAudit.H5GlobalLipAudit.globalLip_iff_target` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipAudit.lean | `SteklovAudit.H5GlobalLipAudit.globalLip_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRows.lean | `SteklovAudit.H5GlobalLipRows.sqrt_lin_prod` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRows.lean | `SteklovAudit.H5GlobalLipRows.scale_le` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRows.lean | `SteklovAudit.H5GlobalLipRows.toGlobalLip_Λ` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRows.lean | `SteklovAudit.H5GlobalLipRows.h5b_of_globalLipRows` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsAudit.lean | `SteklovAudit.H5GlobalLipRowsAudit.rowsAudit_hs2_zero` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsAudit.lean | `SteklovAudit.H5GlobalLipRowsAudit.ofTarget_m` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsAudit.lean | `SteklovAudit.H5GlobalLipRowsAudit.globalLipRows_iff_target` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsAudit.lean | `SteklovAudit.H5GlobalLipRowsAudit.globalLipRows_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEv.lean | `SteklovAudit.H5GlobalLipRowsEv.ofRows_m` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEv.lean | `SteklovAudit.H5GlobalLipRowsEv.toGlobalLipEv_Λ` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEv.lean | `SteklovAudit.H5GlobalLipRowsEv.h5b_of_globalLipRowsEv` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvAudit.lean | `SteklovAudit.H5GlobalLipRowsEvAudit.globalLipRowsEv_iff_target` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvAudit.lean | `SteklovAudit.H5GlobalLipRowsEvAudit.ofTarget_ev_m` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvAudit.lean | `SteklovAudit.H5GlobalLipRowsEvAudit.globalLipRowsEv_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvStrict.lean | `SteklovAudit.H5GlobalLipRowsEvStrict.evD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvStrict.lean | `SteklovAudit.H5GlobalLipRowsEvStrict.evD_massEv` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvStrict.lean | `SteklovAudit.H5GlobalLipRowsEvStrict.evD_J_sq` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsEvStrict.lean | `SteklovAudit.H5GlobalLipRowsEvStrict.evD_no_massLin` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPow.lean | `SteklovAudit.H5GlobalLipRowsPow.rpow_split` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPow.lean | `SteklovAudit.H5GlobalLipRowsPow.sqrt_pow_prod` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPow.lean | `SteklovAudit.H5GlobalLipRowsPow.ofEv_p` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPow.lean | `SteklovAudit.H5GlobalLipRowsPow.toGlobalLipPow_Λ` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPow.lean | `SteklovAudit.H5GlobalLipRowsPow.h5b_of_globalLipRowsPow` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowAudit.lean | `SteklovAudit.H5GlobalLipRowsPowAudit.globalLipRowsPow_iff_target` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowAudit.lean | `SteklovAudit.H5GlobalLipRowsPowAudit.ofTarget_pow_p` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowAudit.lean | `SteklovAudit.H5GlobalLipRowsPowAudit.globalLipRowsPow_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowStrict.lean | `SteklovAudit.H5GlobalLipRowsPowStrict.powD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowStrict.lean | `SteklovAudit.H5GlobalLipRowsPowStrict.powD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowStrict.lean | `SteklovAudit.H5GlobalLipRowsPowStrict.powD_massPow` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowStrict.lean | `SteklovAudit.H5GlobalLipRowsPowStrict.powD_defectPow` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsPowStrict.lean | `SteklovAudit.H5GlobalLipRowsPowStrict.powD_not_massEv` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsStrict.lean | `SteklovAudit.H5GlobalLipRowsStrict.pdeD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsStrict.lean | `SteklovAudit.H5GlobalLipRowsStrict.pdeD_not_massLin` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsStrict.lean | `SteklovAudit.H5GlobalLipRowsStrict.pdeGlobalLip_Λ` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipRowsStrict.lean | `SteklovAudit.H5GlobalLipRowsStrict.pdeGlobalLip_D` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipStrict.lean | `SteklovAudit.H5GlobalLipStrict.steep_selMin_F` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipStrict.lean | `SteklovAudit.H5GlobalLipStrict.steepF_not_lip` | NOT CHECKED (name not found by Lean) |
| H5GlobalLipStrict.lean | `SteklovAudit.H5GlobalLipStrict.steep_selMin_not_lip` | NOT CHECKED (name not found by Lean) |
| H5GlobalVanishNeeded.lean | `SteklovAudit.H5GlobalVanishNeeded.pdeD_pde` | NOT CHECKED (name not found by Lean) |
| H5GlobalVanishNeeded.lean | `SteklovAudit.H5GlobalVanishNeeded.pdeD_prod` | NOT CHECKED (name not found by Lean) |
| H5GlobalVanishNeeded.lean | `SteklovAudit.H5GlobalVanishNeeded.pdeD_not_vanish` | NOT CHECKED (name not found by Lean) |
| H5HiLinear.lean | `SteklovAudit.H5HiLinear.h5b_of_hiLInputs` | NOT CHECKED (name not found by Lean) |
| H5HiLinearAudit.lean | `SteklovAudit.H5HiLinearAudit.hi_term_le` | NOT CHECKED (name not found by Lean) |
| H5HiLinearAudit.lean | `SteklovAudit.H5HiLinearAudit.ofTailEv_nA` | NOT CHECKED (name not found by Lean) |
| H5HiLinearAudit.lean | `SteklovAudit.H5HiLinearAudit.ofTailEv_mHi` | NOT CHECKED (name not found by Lean) |
| H5HiLinearAudit.lean | `SteklovAudit.H5HiLinearAudit.ofTailEv_target` | NOT CHECKED (name not found by Lean) |
| H5HiLinearStrict.lean | `SteklovAudit.H5HiLinearStrict.constTail_hiVanish` | NOT CHECKED (name not found by Lean) |
| H5HiLinearStrict.lean | `SteklovAudit.H5HiLinearStrict.constTail_not_tailEv` | NOT CHECKED (name not found by Lean) |
| H5HiLinearStrict.lean | `SteklovAudit.H5HiLinearStrict.hiL_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.zz_colMissHigh` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.zz_lowCount` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.zz_modelLowCount` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.zz_hmVanish` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.highMass2Witness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.highMass2_rows_not_target` | NOT CHECKED (name not found by Lean) |
| H5HighMass2Audit.lean | `SteklovAudit.H5HighMass2Audit.highMass2_count_not_target` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.z_rowMissHigh` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.highMassWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.zero_rowMissHigh` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.zero_rowMass` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.zero_not_lowCount` | NOT CHECKED (name not found by Lean) |
| H5HighMassAudit.lean | `SteklovAudit.H5HighMassAudit.zero_rowMissHigh_not_mass` | NOT CHECKED (name not found by Lean) |
| H5Joint.lean | `SteklovAudit.H5Joint.h5b_of_jointInputs` | NOT CHECKED (name not found by Lean) |
| H5JointAudit.lean | `SteklovAudit.H5JointAudit.ofHiL_nA` | NOT CHECKED (name not found by Lean) |
| H5JointAudit.lean | `SteklovAudit.H5JointAudit.ofHiL_τ` | NOT CHECKED (name not found by Lean) |
| H5JointAudit.lean | `SteklovAudit.H5JointAudit.ofHiL_target` | NOT CHECKED (name not found by Lean) |
| H5JointCutoffNeeded.lean | `SteklovAudit.H5JointCutoffNeeded.sq_target_fails` | NOT CHECKED (name not found by Lean) |
| H5JointCutoffNeeded.lean | `SteklovAudit.H5JointCutoffNeeded.zero_rows_hold` | NOT CHECKED (name not found by Lean) |
| H5JointCutoffNeeded.lean | `SteklovAudit.H5JointCutoffNeeded.cutoff_row_needed` | NOT CHECKED (name not found by Lean) |
| H5JointIff.lean | `SteklovAudit.H5JointIff.jointInputs_iff_target` | NOT CHECKED (name not found by Lean) |
| H5JointIff.lean | `SteklovAudit.H5JointIff.jointInputs_nonempty` | NOT CHECKED (name not found by Lean) |
| H5JointSel.lean | `SteklovAudit.H5JointSel.h5b_of_jointSelInputs` | NOT CHECKED (name not found by Lean) |
| H5JointSelAudit.lean | `SteklovAudit.H5JointSelAudit.ofJoint_τ` | NOT CHECKED (name not found by Lean) |
| H5JointSelAudit.lean | `SteklovAudit.H5JointSelAudit.ofJoint_target` | NOT CHECKED (name not found by Lean) |
| H5JointSelAudit.lean | `SteklovAudit.H5JointSelAudit.sel_holds` | NOT CHECKED (name not found by Lean) |
| H5JointSelAudit.lean | `SteklovAudit.H5JointSelAudit.const_fails` | NOT CHECKED (name not found by Lean) |
| H5JointSelAudit.lean | `SteklovAudit.H5JointSelAudit.sel_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5JointSelIff.lean | `SteklovAudit.H5JointSelIff.selInputs_iff_target` | NOT CHECKED (name not found by Lean) |
| H5JointSelIff.lean | `SteklovAudit.H5JointSelIff.selInputs_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5JointStrict.lean | `SteklovAudit.H5JointStrict.joint_holds` | NOT CHECKED (name not found by Lean) |
| H5JointStrict.lean | `SteklovAudit.H5JointStrict.lowEvery_fails` | NOT CHECKED (name not found by Lean) |
| H5JointStrict.lean | `SteklovAudit.H5JointStrict.joint_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.abs_sub_le_of_deriv_bound` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.abs_sub_le_of_deriv_bound_Iic` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.lipHi_of_deriv_bound` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.le_of_not_hiE` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.lipLo_of_deriv_bound_le` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.hΛ0_of_deriv_bound` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.lipHi_field` | NOT CHECKED (name not found by Lean) |
| H5LipRows.lean | `SteklovAudit.H5LipRows.lipLo_field` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.not_hiE_le` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.mask_sq_le_row` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.low_mask_le_rows` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.rows_le_card` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.lowMass_of_bessel_lowCount` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.lowDefect_of_bessel_lowCount` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.card_filter_le_two` | NOT CHECKED (name not found by Lean) |
| H5LowCount.lean | `SteklovAudit.H5LowCount.lowCount_nonjunk` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.card_low_le_floor` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.lowCount_of_linear_growth` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.lowCount_of_linear_growth_abs` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.exists_lowCount_of_linear_growth` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.ceil_count` | NOT CHECKED (name not found by Lean) |
| H5LowCountGrowth.lean | `SteklovAudit.H5LowCountGrowth.count_not_lowCount` | NOT CHECKED (name not found by Lean) |
| H5LowLinear.lean | `SteklovAudit.H5LowLinear.h5b_of_lowLInputs` | NOT CHECKED (name not found by Lean) |
| H5LowLinearAudit.lean | `SteklovAudit.H5LowLinearAudit.low_term_le` | NOT CHECKED (name not found by Lean) |
| H5LowLinearAudit.lean | `SteklovAudit.H5LowLinearAudit.ofInputs_nA` | NOT CHECKED (name not found by Lean) |
| H5LowLinearAudit.lean | `SteklovAudit.H5LowLinearAudit.ofInputs_κ2` | NOT CHECKED (name not found by Lean) |
| H5LowLinearAudit.lean | `SteklovAudit.H5LowLinearAudit.ofInputs_mLo` | NOT CHECKED (name not found by Lean) |
| H5LowLinearAudit.lean | `SteklovAudit.H5LowLinearAudit.ofInputs_target` | NOT CHECKED (name not found by Lean) |
| H5LowLinearRows.lean | `SteklovAudit.H5LowLinearRows.lowMass_le_count` | NOT CHECKED (name not found by Lean) |
| H5LowLinearRows.lean | `SteklovAudit.H5LowLinearRows.lowDefect_le_count` | NOT CHECKED (name not found by Lean) |
| H5LowLinearRows.lean | `SteklovAudit.H5LowLinearRows.lowRows_of_linearCount` | NOT CHECKED (name not found by Lean) |
| H5LowLinearRows.lean | `SteklovAudit.H5LowLinearRows.sqrt_linear_rows` | NOT CHECKED (name not found by Lean) |
| H5LowLinearRows.lean | `SteklovAudit.H5LowLinearRows.lowVanish_of_linear` | NOT CHECKED (name not found by Lean) |
| H5LowLinearStrict.lean | `SteklovAudit.H5LowLinearStrict.floor_le_one_add_abs` | NOT CHECKED (name not found by Lean) |
| H5LowLinearStrict.lean | `SteklovAudit.H5LowLinearStrict.flatD_filter_card_le` | NOT CHECKED (name not found by Lean) |
| H5LowLinearStrict.lean | `SteklovAudit.H5LowLinearStrict.flatD_linearCount` | NOT CHECKED (name not found by Lean) |
| H5LowLinearStrict.lean | `SteklovAudit.H5LowLinearStrict.flatD_linearCount_exists` | NOT CHECKED (name not found by Lean) |
| H5LowLinearStrict.lean | `SteklovAudit.H5LowLinearStrict.linearCount_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.abs_sub_le_of_low` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.low_K_sq_le` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.low_mask_K_sq_le` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.hs2_low_K_le` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowDefect_of_lowMass` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowDefect_field` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowDefect_of_LowMass` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.hs2_one` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowCounter_nonneg` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowCounter_pde` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowCounter_low_mass` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowMass_not_of_pde` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowMass_row_fails` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowMass_of_J_zero` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowMass_satisfiable` | NOT CHECKED (name not found by Lean) |
| H5LowMass.lean | `SteklovAudit.H5LowMass.lowMass_not_target` | NOT CHECKED (name not found by Lean) |
| H5MaskSplit.lean | `SteklovAudit.H5MaskSplit.hs2_mask_add_compl` | NOT CHECKED (name not found by Lean) |
| H5MaskSplit.lean | `SteklovAudit.H5MaskSplit.sqrt_mul_add_sqrt_mul_le` | NOT CHECKED (name not found by Lean) |
| H5MaskSplit.lean | `SteklovAudit.H5MaskSplit.split_le_unsplit` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.z_rowMiss` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.z_colMiss` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.massWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.atL_rowDefect` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.atL_rowMass` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.atL_rowMiss_fails` | NOT CHECKED (name not found by Lean) |
| H5MassAudit.lean | `SteklovAudit.H5MassAudit.mass_stronger_than_defect` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_defectSmall` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_not_massEv` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_prod` | NOT CHECKED (name not found by Lean) |
| H5MassEvNeeded.lean | `SteklovAudit.H5MassEvNeeded.bigD_not_vanish` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.sum_one_eq_card` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.mass_of_bessel_count` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.pde_of_bessel_count` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.idJ_row` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.idJ_hs2` | NOT CHECKED (name not found by Lean) |
| H5MassRow.lean | `SteklovAudit.H5MassRow.bessel_count_nonjunk` | NOT CHECKED (name not found by Lean) |
| H5MassSplit.lean | `SteklovAudit.H5MassSplit.missing_nonneg` | NOT CHECKED (name not found by Lean) |
| H5MassSplit.lean | `SteklovAudit.H5MassSplit.missing_le_one` | NOT CHECKED (name not found by Lean) |
| H5MassSplit.lean | `SteklovAudit.H5MassSplit.missing_split` | NOT CHECKED (name not found by Lean) |
| H5MassSplit.lean | `SteklovAudit.H5MassSplit.h5b_of_high_mass` | NOT CHECKED (name not found by Lean) |
| H5MissingMass.lean | `SteklovAudit.H5MissingMass.vanish_const_mul` | NOT CHECKED (name not found by Lean) |
| H5MissingMass.lean | `SteklovAudit.H5MissingMass.toCounts_k1` | NOT CHECKED (name not found by Lean) |
| H5MissingMass.lean | `SteklovAudit.H5MissingMass.toCounts_k2` | NOT CHECKED (name not found by Lean) |
| H5MissingMass.lean | `SteklovAudit.H5MissingMass.h5b_of_mass` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wN_le_one` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_K` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_sum` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_bessel` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_count` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_defect` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_tail` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.wData_lowCount` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.w_cutoff` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.paperWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.paperWitness_nonjunk` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.paper_rows_not_target` | NOT CHECKED (name not found by Lean) |
| H5PaperAudit.lean | `SteklovAudit.H5PaperAudit.paper_iff_target` | NOT CHECKED (name not found by Lean) |
| H5PaperRows.lean | `SteklovAudit.H5PaperRows.toWeak_F` | NOT CHECKED (name not found by Lean) |
| H5PaperRows.lean | `SteklovAudit.H5PaperRows.toWeak_m` | NOT CHECKED (name not found by Lean) |
| H5PaperRows.lean | `SteklovAudit.H5PaperRows.toWeak_disc` | NOT CHECKED (name not found by Lean) |
| H5PaperRows.lean | `SteklovAudit.H5PaperRows.h5b_of_paper` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.rowMiss_of_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.colMiss_of_colNorm` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.card_eq_of_norms` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.zero_vanish` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.h5b_of_norm` | NOT CHECKED (name not found by Lean) |
| H5Parseval.lean | `SteklovAudit.H5Parseval.norm_card_eq` | NOT CHECKED (name not found by Lean) |
| H5PinnedCutoffIsTarget.lean | `SteklovAudit.H5PinnedCutoffIsTarget.cutoffVanish_of_target` | NOT CHECKED (name not found by Lean) |
| H5PinnedCutoffIsTarget.lean | `SteklovAudit.H5PinnedCutoffIsTarget.pinned_iff_target_of_dataRows` | NOT CHECKED (name not found by Lean) |
| H5PinnedCutoffVanish.lean | `SteklovAudit.H5PinnedCutoffVanish.ofCore_disc` | NOT CHECKED (name not found by Lean) |
| H5PinnedCutoffVanish.lean | `SteklovAudit.H5PinnedCutoffVanish.pinned_iff_core` | NOT CHECKED (name not found by Lean) |
| H5PinnedCutoffVanish.lean | `SteklovAudit.H5PinnedCutoffVanish.h5b_of_pinnedCore` | NOT CHECKED (name not found by Lean) |
| H5PinnedDataRows.lean | `SteklovAudit.H5PinnedDataRows.dataOf_Λ` | NOT CHECKED (name not found by Lean) |
| H5PinnedDataRows.lean | `SteklovAudit.H5PinnedDataRows.sumLittleO_of_dataRows` | NOT CHECKED (name not found by Lean) |
| H5PinnedDataRows.lean | `SteklovAudit.H5PinnedDataRows.pinned_iff_dataRows_core` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.decay_sum` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.decayD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.decayD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.decay_defect_pos` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.decayRows_m` | NOT CHECKED (name not found by Lean) |
| H5PinnedNonvacuous.lean | `SteklovAudit.H5PinnedNonvacuous.pinned_nonempty_decay` | NOT CHECKED (name not found by Lean) |
| H5PinnedNotTarget.lean | `SteklovAudit.H5PinnedNotTarget.bump_sum` | NOT CHECKED (name not found by Lean) |
| H5PinnedNotTarget.lean | `SteklovAudit.H5PinnedNotTarget.target_zero` | NOT CHECKED (name not found by Lean) |
| H5PinnedNotTarget.lean | `SteklovAudit.H5PinnedNotTarget.not_pinned_bump` | NOT CHECKED (name not found by Lean) |
| H5PinnedNotTarget.lean | `SteklovAudit.H5PinnedNotTarget.pinned_strictly_stronger` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLip.lean | `SteklovAudit.H5PinnedPtsLip.trace_transfer_pts` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLip.lean | `SteklovAudit.H5PinnedPtsLip.ofDataRows_Λ` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLip.lean | `SteklovAudit.H5PinnedPtsLip.sumLittleO_of_ptsRows` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLip.lean | `SteklovAudit.H5PinnedPtsLip.h5b_of_ptsRows` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLipStrict.lean | `SteklovAudit.H5PinnedPtsLipStrict.ptsRows_flat` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLipStrict.lean | `SteklovAudit.H5PinnedPtsLipStrict.not_dataRows_flat` | NOT CHECKED (name not found by Lean) |
| H5PinnedPtsLipStrict.lean | `SteklovAudit.H5PinnedPtsLipStrict.ptsLip_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5PinnedRows.lean | `SteklovAudit.H5PinnedRows.toRows_D` | NOT CHECKED (name not found by Lean) |
| H5PinnedRows.lean | `SteklovAudit.H5PinnedRows.toRows_F` | NOT CHECKED (name not found by Lean) |
| H5PinnedRows.lean | `SteklovAudit.H5PinnedRows.h5b_of_pinnedRows` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPow.lean | `SteklovAudit.H5PinnedRowsPow.toRowsPow_D` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPow.lean | `SteklovAudit.H5PinnedRowsPow.ofPinned_p` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPow.lean | `SteklovAudit.H5PinnedRowsPow.h5b_of_pinnedRowsPow` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.q_sum` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.qD_hs2J` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.qD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.pinnedPow_nonempty_q` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.not_pinnedRows_q` | NOT CHECKED (name not found by Lean) |
| H5PinnedRowsPowStrict.lean | `SteklovAudit.H5PinnedRowsPowStrict.pinnedPow_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5PinnedSumSmall.lean | `SteklovAudit.H5PinnedSumSmall.pinned_sum_littleO` | NOT CHECKED (name not found by Lean) |
| H5PinnedSumSmall.lean | `SteklovAudit.H5PinnedSumSmall.pinned_target_and_sum` | NOT CHECKED (name not found by Lean) |
| H5PinnedSumSmall.lean | `SteklovAudit.H5PinnedSumSmall.not_pinned_of_sum_large` | NOT CHECKED (name not found by Lean) |
| H5PinnedZeroAudit.lean | `SteklovAudit.H5PinnedZeroAudit.pinnedZero_disc` | NOT CHECKED (name not found by Lean) |
| H5PinnedZeroAudit.lean | `SteklovAudit.H5PinnedZeroAudit.pinnedZero_iff_target` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_a` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_b` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_J` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_K` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.sum_sum_reindex` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.hs2_reindex` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_rowSq` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_colSq` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_rowMass` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_colMass` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_hs2K` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_tail` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_lowCount` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_smoothedA` | NOT CHECKED (name not found by Lean) |
| H5Reindex.lean | `SteklovAudit.H5Reindex.reindex_smoothedB` | NOT CHECKED (name not found by Lean) |
| H5RowNormEv.lean | `SteklovAudit.H5RowNormEv.rowNormEv_colMiss` | NOT CHECKED (name not found by Lean) |
| H5RowNormEv.lean | `SteklovAudit.H5RowNormEv.toSmoothedEv_nA` | NOT CHECKED (name not found by Lean) |
| H5RowNormEv.lean | `SteklovAudit.H5RowNormEv.h5b_of_rowNormEv` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_colBessel` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_K` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_hs2K` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_defect` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_tail` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rnD_lowCount` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rowNormEvWitness_genuine` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rowNormEv_not_rowNorm` | NOT CHECKED (name not found by Lean) |
| H5RowNormEvAudit.lean | `SteklovAudit.H5RowNormEvAudit.rowNormEvWitness_target` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.normWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.rowNorm_count_neg_one` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapD_colBessel` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapD_count` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapD_defect` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapD_tail` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapD_lowCount` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.gapRate_vanish` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.rowNormWitness_nonsquare` | NOT CHECKED (name not found by Lean) |
| H5RowNormWitness.lean | `SteklovAudit.H5RowNormWitness.rowNormWitness_target` | NOT CHECKED (name not found by Lean) |
| H5SelDirect.lean | `SteklovAudit.H5SelDirect.h5b_of_selDirectInputs` | NOT CHECKED (name not found by Lean) |
| H5SelDirectAudit.lean | `SteklovAudit.H5SelDirectAudit.ofSel_Λ0` | NOT CHECKED (name not found by Lean) |
| H5SelDirectAudit.lean | `SteklovAudit.H5SelDirectAudit.ofSel_target` | NOT CHECKED (name not found by Lean) |
| H5SelDirectIff.lean | `SteklovAudit.H5SelDirectIff.selDirect_iff_target` | NOT CHECKED (name not found by Lean) |
| H5SelDirectIff.lean | `SteklovAudit.H5SelDirectIff.selDirect_nonempty_zero` | NOT CHECKED (name not found by Lean) |
| H5SelMin.lean | `SteklovAudit.H5SelMin.h5b_of_selMinInputs` | NOT CHECKED (name not found by Lean) |
| H5SelMin.lean | `SteklovAudit.H5SelMin.forgetPde_Λ0` | NOT CHECKED (name not found by Lean) |
| H5SelMin.lean | `SteklovAudit.H5SelMin.forgetPde_target` | NOT CHECKED (name not found by Lean) |
| H5SelMinStrict.lean | `SteklovAudit.H5SelMinStrict.bigD_K` | NOT CHECKED (name not found by Lean) |
| H5SelMinStrict.lean | `SteklovAudit.H5SelMinStrict.bigD_selMin_target` | NOT CHECKED (name not found by Lean) |
| H5SelMinStrict.lean | `SteklovAudit.H5SelMinStrict.hs2_bigD_J` | NOT CHECKED (name not found by Lean) |
| H5SelMinStrict.lean | `SteklovAudit.H5SelMinStrict.bigD_not_pde` | NOT CHECKED (name not found by Lean) |
| H5SelMinStrict.lean | `SteklovAudit.H5SelMinStrict.selMin_without_pde` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.wData_rowTrace` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.wData_colTrace` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.w_trueSide` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.w_modelSide` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.zeroDisc_vanish` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.zero_bound` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.sideWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.not_target_mirror` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.model_side_not_target` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.true_side_not_target` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.sides_imply_cutoff` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.arctan_abs_le_two` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.fin1_cutoff` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.fin1_rowTrace` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.fin1_trueSide_fails` | NOT CHECKED (name not found by Lean) |
| H5SideAudit.lean | `SteklovAudit.H5SideAudit.cutoff_not_sides` | NOT CHECKED (name not found by Lean) |
| H5SideRows.lean | `SteklovAudit.H5SideRows.toPaper_disc` | NOT CHECKED (name not found by Lean) |
| H5SideRows.lean | `SteklovAudit.H5SideRows.toPaper_P` | NOT CHECKED (name not found by Lean) |
| H5SideRows.lean | `SteklovAudit.H5SideRows.h5b_of_sides` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smCeil_rowMass` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smoothed_rowMiss_forces` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smCeil_E` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smCeil_Emod` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smCeil_not_target` | NOT CHECKED (name not found by Lean) |
| H5SmoothedAudit.lean | `SteklovAudit.H5SmoothedAudit.smoothed_needs_mass` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_rowMass_zero` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_rowMiss_zero` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_colMass` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smoothed_colMiss_forces` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_E` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_Emod` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smCol_not_target` | NOT CHECKED (name not found by Lean) |
| H5SmoothedColAudit.lean | `SteklovAudit.H5SmoothedColAudit.smoothed_needs_colMass` | NOT CHECKED (name not found by Lean) |
| H5SmoothedHigh.lean | `SteklovAudit.H5SmoothedHigh.smoothedHigh_diffCount` | NOT CHECKED (name not found by Lean) |
| H5SmoothedHigh.lean | `SteklovAudit.H5SmoothedHigh.h5b_of_smoothedHigh2` | NOT CHECKED (name not found by Lean) |
| H5SmoothedIdent.lean | `SteklovAudit.H5SmoothedIdent.smoothed_diffCount` | NOT CHECKED (name not found by Lean) |
| H5SmoothedIdent.lean | `SteklovAudit.H5SmoothedIdent.h5b_of_smoothed` | NOT CHECKED (name not found by Lean) |
| H5SmoothedIdent.lean | `SteklovAudit.H5SmoothedIdent.diffCount_iff_ident` | NOT CHECKED (name not found by Lean) |
| H5SmoothedWitness.lean | `SteklovAudit.H5SmoothedWitness.toSmoothed_Esm` | NOT CHECKED (name not found by Lean) |
| H5SmoothedWitness.lean | `SteklovAudit.H5SmoothedWitness.toSmoothed_Emodsm` | NOT CHECKED (name not found by Lean) |
| H5SmoothedWitness.lean | `SteklovAudit.H5SmoothedWitness.toSmoothed_P` | NOT CHECKED (name not found by Lean) |
| H5SmoothedWitness.lean | `SteklovAudit.H5SmoothedWitness.smoothedWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5SmoothedWitness.lean | `SteklovAudit.H5SmoothedWitness.smoothed_witness_target` | NOT CHECKED (name not found by Lean) |
| H5Split.lean | `SteklovAudit.H5Split.trace_little_o_of_rows` | NOT CHECKED (name not found by Lean) |
| H5Split.lean | `SteklovAudit.H5Split.h5b_of_cutoff_and_trace` | NOT CHECKED (name not found by Lean) |
| H5Split.lean | `SteklovAudit.H5Split.h5b_via_split` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.hs2_mask_split` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.defect_le_tail_add_low` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.hs2_fin_one` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.counterData_pde` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.counterData_hi_mask` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.defect_not_imp_tail` | NOT CHECKED (name not found by Lean) |
| H5TailAudit.lean | `SteklovAudit.H5TailAudit.tail_row_fails` | NOT CHECKED (name not found by Lean) |
| H5TailEv.lean | `SteklovAudit.H5TailEv.h5b_of_tailEv` | NOT CHECKED (name not found by Lean) |
| H5TailEvAudit.lean | `SteklovAudit.H5TailEvAudit.ofLowL_nA` | NOT CHECKED (name not found by Lean) |
| H5TailEvAudit.lean | `SteklovAudit.H5TailEvAudit.ofLowL_τ` | NOT CHECKED (name not found by Lean) |
| H5TailEvAudit.lean | `SteklovAudit.H5TailEvAudit.ofLowL_target` | NOT CHECKED (name not found by Lean) |
| H5TailEvStrict.lean | `SteklovAudit.H5TailEvStrict.bumpTail_eventual` | NOT CHECKED (name not found by Lean) |
| H5TailEvStrict.lean | `SteklovAudit.H5TailEvStrict.bumpTail_not_uniform` | NOT CHECKED (name not found by Lean) |
| H5TailEvStrict.lean | `SteklovAudit.H5TailEvStrict.tailEv_strictly_weaker` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.div_le_of_rate` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.tailVanish_of_power` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.tailVanish_field` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.invRate` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.invRate_vanish` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.not_target_double` | NOT CHECKED (name not found by Lean) |
| H5TailRate.lean | `SteklovAudit.H5TailRate.tail_rate_not_target` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.weak_hs2_zero` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.zeroData_J` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.zeroData_K` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.zeroData_pde` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.zeroData_tail` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.zeroRate` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.weakWitness_nonempty` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.weak_rows_not_target` | NOT CHECKED (name not found by Lean) |
| H5WeakAudit.lean | `SteklovAudit.H5WeakAudit.weak_iff_target` | NOT CHECKED (name not found by Lean) |
| H5WeakRows.lean | `SteklovAudit.H5WeakRows.toInputs_κ2` | NOT CHECKED (name not found by Lean) |
| H5WeakRows.lean | `SteklovAudit.H5WeakRows.toInputs_disc` | NOT CHECKED (name not found by Lean) |
| H5WeakRows.lean | `SteklovAudit.H5WeakRows.h5b_of_weak` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.hasDerivAt_shift` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.deriv_shift` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.differentiable_shift` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipHi_of_profile` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipLo_of_profile` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipHi_field_profile` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipLo_field_profile` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.profLam_nonneg` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipLo_profLam` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.profLam_vanish` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.eventually_le_of_tendsto` | NOT CHECKED (name not found by Lean) |
| H5WindowProfile.lean | `SteklovAudit.H5WindowProfile.lipGroup_of_profile` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_hasDerivAt'` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_deriv_eq` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_differentiable'` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_deriv_le_one` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_tail` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctanTail_small` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_lipGroup` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_profile_nonjunk` | NOT CHECKED (name not found by Lean) |
| H5WindowWitness.lean | `SteklovAudit.H5WindowWitness.arctan_shift_nonconst` | NOT CHECKED (name not found by Lean) |
| H5bQuantifierOrder.lean | `SteklovAudit.H5bQuantifierOrder.model_target` | NOT CHECKED (name not found by Lean) |
| H5bQuantifierOrder.lean | `SteklovAudit.H5bQuantifierOrder.model_not_uniform` | NOT CHECKED (name not found by Lean) |
| H5bQuantifierOrder.lean | `SteklovAudit.H5bQuantifierOrder.model_small_gamma_eq` | NOT CHECKED (name not found by Lean) |
| H5bQuantifierOrder.lean | `SteklovAudit.H5bQuantifierOrder.model_limit_not_littleO` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.re_star_mul_self` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_nonneg` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_zero` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_eq_trace` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.unitary_ct_mul_self` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.unitary_mul_ct_self` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_unitary_left` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_unitary_right` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependence.lean | `SteklovAudit.HSBasisIndependence.hsSq_conj_unitary` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependenceReal.lean | `SteklovAudit.HSBasisIndependence.parseval_sq` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependenceReal.lean | `SteklovAudit.HSBasisIndependence.hs_sum_eq_double` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependenceReal.lean | `SteklovAudit.HSBasisIndependence.hs_sum_eq_adjoint` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependenceReal.lean | `SteklovAudit.HSBasisIndependence.hs_sum_basis_indep` | NOT CHECKED (name not found by Lean) |
| HSBasisIndependenceReal.lean | `SteklovAudit.HSBasisIndependence.hs_sum_id` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.scalarDiag_diag` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.scalarDiag_off` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.hs2_scalarDiag` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.trace_scalarDiag` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.hs2_tendsto_zero` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.trace_const` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.no_dimension_free_trace_bound` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.rank_amplification_equality` | NOT CHECKED (name not found by Lean) |
| HSNoTrace.lean | `SteklovAudit.HSNoTrace.sqrt_rank_equality` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.beta_scaling` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.heat_convolution` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.time_integral` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.time_integrable` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.beta_integrable` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.heat_trace_integrable` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.fiber_scaling` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.edge_heat_limit` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.integral_inv_one_add_exp` | NOT CHECKED (name not found by Lean) |
| HeatFiber.lean | `SteklovAudit.HeatFiber.cosh_integral_log_bound` | NOT CHECKED (name not found by Lean) |
| IdentificationBudget.lean | `SteklovAudit.IdentificationBudget.trace_proj` | NOT CHECKED (name not found by Lean) |
| IdentificationBudget.lean | `SteklovAudit.IdentificationBudget.trace_JPJt` | NOT CHECKED (name not found by Lean) |
| IdentificationBudget.lean | `SteklovAudit.IdentificationBudget.identification_identity` | NOT CHECKED (name not found by Lean) |
| IdentificationBudget.lean | `SteklovAudit.IdentificationBudget.identification_budget_coords` | NOT CHECKED (name not found by Lean) |
| IdentificationBudget.lean | `SteklovAudit.IdentificationBudget.identification_budget_contraction` | NOT CHECKED (name not found by Lean) |
| IdentificationBudgetData.lean | `SteklovAudit.AbstractTransfer.budget_identity` | NOT CHECKED (name not found by Lean) |
| IdentificationBudgetData.lean | `SteklovAudit.AbstractTransfer.budget_bound` | NOT CHECKED (name not found by Lean) |
| IdentificationBudgetData.lean | `SteklovAudit.AbstractTransfer.defect_terms_nonneg` | NOT CHECKED (name not found by Lean) |
| IdentificationBudgetData.lean | `SteklovAudit.AbstractTransfer.signed_trace_cancels` | NOT CHECKED (name not found by Lean) |
| LeakageLayerCake.lean | `SteklovAudit.LeakageLayerCake.leakage_gap` | NOT CHECKED (name not found by Lean) |
| LeakageLayerCake.lean | `SteklovAudit.LeakageLayerCake.layer_cake_sq` | NOT CHECKED (name not found by Lean) |
| LeakageLayerCake.lean | `SteklovAudit.LeakageLayerCake.indicator_integrable` | NOT CHECKED (name not found by Lean) |
| LeakageLayerCake.lean | `SteklovAudit.LeakageLayerCake.layer_cake_sum` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.cutTriv_len` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.loc_unit` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.areaOf_unit` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.zero_piece` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.one_piece` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousC6.lean | `SteklovAudit.LedgerNonvacuousC6.nonvacuous_C6` | NOT CHECKED (name not found by Lean) |
| LedgerNonvacuousD5.lean | `SteklovAudit.LedgerNonvacuousD5.nonvacuous_D5` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.tetraAngle_mem` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.abs_add_four_le` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.two_scale_of_inputs` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.theorem_11_1_of_inputs` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.formula_11_4_of_inputs` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.nonvacuous` | NOT CHECKED (name not found by Lean) |
| MainConditional.lean | `SteklovAudit.MainConditional.conclusion_nontrivial` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFamily.lean | `SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_family` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFamily.lean | `SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_family'` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFamily.lean | `SteklovAudit.ModelEdgeLawGammaFamily.edge_law_of_gamma_main` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFamily.lean | `SteklovAudit.ModelEdgeLawGammaFamily.gamma_term_must_shrink` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFree.lean | `SteklovAudit.ModelEdgeLawGammaFree.eta_of_isLittleO` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFree.lean | `SteklovAudit.ModelEdgeLawGammaFree.model_law_gamma_free` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFree.lean | `SteklovAudit.ModelEdgeLawGammaFree.model_law_gamma_free_nonvacuous` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawGammaFree.lean | `SteklovAudit.ModelEdgeLawGammaFree.model_law_gamma_free_example` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.k_integral` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.pertrace_scalar` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.smoothed_ramp` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.smoothed_ramp_sq` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.smoothed_ramp_neg` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.dyadic_sum_closed` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.dyadic_sum_le` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.littleO_of_bounded` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.model_law_of_decomposition` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawReduction.lean | `SteklovAudit.ModelEdgeLawReduction.model_law_nonvacuous` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawSixEdges.lean | `SteklovAudit.ModelEdgeLawSixEdges.finset_sum_littleO` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawSixEdges.lean | `SteklovAudit.ModelEdgeLawSixEdges.six_edge_law` | NOT CHECKED (name not found by Lean) |
| ModelEdgeLawSixEdges.lean | `SteklovAudit.ModelEdgeLawSixEdges.six_equal_edges` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.trA_eq` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.multichart_trace` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.ex_row` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.ex_partition` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.sharp_example_hs2` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.sharp_example_trace` | NOT CHECKED (name not found by Lean) |
| MultiChartTrace.lean | `SteklovAudit.MultiChartTrace.sharp_example_norm` | NOT CHECKED (name not found by Lean) |
| PartitionTrace.lean | `SteklovAudit.PartitionTrace.diag_conj_entry` | NOT CHECKED (name not found by Lean) |
| PartitionTrace.lean | `SteklovAudit.PartitionTrace.trace_squared_partition` | NOT CHECKED (name not found by Lean) |
| PartitionTrace.lean | `SteklovAudit.PartitionTrace.trace_split3` | NOT CHECKED (name not found by Lean) |
| PartitionTrace.lean | `SteklovAudit.PartitionTrace.area_additive` | NOT CHECKED (name not found by Lean) |
| PartitionTrace.lean | `SteklovAudit.PartitionTrace.theorem_11_1_of_C5` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.rpow_pos'` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.rpow_neg_le_one` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.eventually_rpow_neg_le` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.inv_sq_rpow_neg` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.hs_term_bound` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.power_little_o` | NOT CHECKED (name not found by Lean) |
| PowerShiftTransfer.lean | `SteklovAudit.PowerShiftTransfer.sharp_law_transfer_power` | NOT CHECKED (name not found by Lean) |
| PropagatorTrace.lean | `SteklovAudit.PropagatorTrace.diag_K_le_hs2` | NOT CHECKED (name not found by Lean) |
| PropagatorTrace.lean | `SteklovAudit.PropagatorTrace.propagator_trace_sq` | NOT CHECKED (name not found by Lean) |
| PropagatorTrace.lean | `SteklovAudit.PropagatorTrace.propagator_trace` | NOT CHECKED (name not found by Lean) |
| PropagatorTrace.lean | `SteklovAudit.PropagatorTrace.propagator_trace_of_inputs` | NOT CHECKED (name not found by Lean) |
| RealToIntegerLaw.lean | `SteklovAudit.RealToIntegerLaw.twoTerm_eq_real` | NOT CHECKED (name not found by Lean) |
| RealToIntegerLaw.lean | `SteklovAudit.RealToIntegerLaw.integer_law_of_real_law` | NOT CHECKED (name not found by Lean) |
| RealToIntegerLaw.lean | `SteklovAudit.RealToIntegerLaw.integer_law_of_inputs` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.slopes_phi0` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.slopes_phi1` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.slopes_phi2` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.slopes_phi3` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.residual_energy_phi0` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.residual_energy_phi1` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.residual_energy_phi2` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.residual_energy_phi3` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.normalized_energy` | NOT CHECKED (name not found by Lean) |
| ResidualLink.lean | `SteklovAudit.ResidualLink.residual_defect_constant` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.basis_hasSum_sq` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.residual_coordinate` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.residual_hasSum_sq` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.residual_first_moment` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.finite_probe_hasSum` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.trace_gram` | NOT CHECKED (name not found by Lean) |
| ReviewCandidates.lean | `SteklovAudit.ReviewCandidates.projection_frobenius_contracts` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.spectral_sums_of_operator` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.summable_energy_tail` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.square_sum_strong_tail` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.hs_right_tail_of_adjoint_strong` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.centered_second_order_bound` | NOT CHECKED (name not found by Lean) |
| ReviewExtensions.lean | `SteklovAudit.ReviewExtensions.countable_centered_remainder_bound` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.hasDerivAt_phiS` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.abs_phiS_le` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.osc_riesz_bound` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.hasDerivAt_Fc` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.deriv_Fc_pos` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.Fc_monotoneOn` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.Nc_monotone` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.Nc_eq` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.Nc_not_sharp` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.Nc_riesz` | NOT CHECKED (name not found by Lean) |
| RieszCounterexample.lean | `SteklovAudit.RieszCounterexample.riesz_does_not_imply_sharp` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.int_rpow` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.kernel_moment0` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.kernel_moment1` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.kernel_moment2` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.kernel_ii` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.kernel_mul_ii` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.riesz_of_sharp` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.riesz_single` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.riesz_finite` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.riesz_of_sharpLaw` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.leading_coefficient` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.riesz_of_inputs` | NOT CHECKED (name not found by Lean) |
| RieszMeans.lean | `SteklovAudit.RieszMeans.first_riesz_coefficients_paper` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.hasDerivAt_gd` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.sech_pi_nonneg` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.tendsto_gd` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.gd_zero` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.integrableOn_sech_pi` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.integral_sech_pi` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.sinh_ne_zero_of_pos` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.integrand_right_angle` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.integrableOn_dihedral_right_angle` | NOT CHECKED (name not found by Lean) |
| RightAngleCalibration.lean | `SteklovAudit.RightAngleCalibration.dihedralCoeff_right_angle` | NOT CHECKED (name not found by Lean) |
| RpowScale.lean | `SteklovAudit.RpowScale.rpow_neg_pos` | NOT CHECKED (name not found by Lean) |
| RpowScale.lean | `SteklovAudit.RpowScale.rpow_neg_le_one` | NOT CHECKED (name not found by Lean) |
| RpowScale.lean | `SteklovAudit.RpowScale.eventually_rpow_neg_le` | NOT CHECKED (name not found by Lean) |
| RpowScale.lean | `SteklovAudit.RpowScale.hs_term_littleO` | NOT CHECKED (name not found by Lean) |
| RpowScale.lean | `SteklovAudit.RpowScale.sharp_law_transfer_rpow` | NOT CHECKED (name not found by Lean) |
| ScalingLaw.lean | `SteklovAudit.ScalingLaw.weyl_scale` | NOT CHECKED (name not found by Lean) |
| ScalingLaw.lean | `SteklovAudit.ScalingLaw.law_rescale` | NOT CHECKED (name not found by Lean) |
| ScalingLaw.lean | `SteklovAudit.ScalingLaw.law_scaling` | NOT CHECKED (name not found by Lean) |
| ScalingLaw.lean | `SteklovAudit.ScalingLaw.law_unscaling` | NOT CHECKED (name not found by Lean) |
| ScalingLaw.lean | `SteklovAudit.ScalingLaw.law_scaling_iff` | NOT CHECKED (name not found by Lean) |
| Section11AllFixedScales.lean | `SteklovAudit.quadratic_fixed_shift_plus` | NOT CHECKED (name not found by Lean) |
| Section11AllFixedScales.lean | `SteklovAudit.quadratic_fixed_shift_minus` | NOT CHECKED (name not found by Lean) |
| Section11AllFixedScales.lean | `SteklovAudit.monotone_fixed_window` | NOT CHECKED (name not found by Lean) |
| Section11ApproximateFixedScales.lean | `SteklovAudit.shift_linear_normalized` | NOT CHECKED (name not found by Lean) |
| Section11ApproximateFixedScales.lean | `SteklovAudit.shift_linear_normalized_minus` | NOT CHECKED (name not found by Lean) |
| Section11ApproximateFixedScales.lean | `SteklovAudit.monotone_window_order` | NOT CHECKED (name not found by Lean) |
| Section11FiniteScaleBracket.lean | `SteklovAudit.quadratic_shift_plus` | NOT CHECKED (name not found by Lean) |
| Section11FiniteScaleBracket.lean | `SteklovAudit.quadratic_shift_minus` | NOT CHECKED (name not found by Lean) |
| Section11FiniteScaleBracket.lean | `SteklovAudit.alternating_pair_identity` | NOT CHECKED (name not found by Lean) |
| Section11ShiftBudgetOptimization.lean | `SteklovAudit.cubic_factor` | NOT CHECKED (name not found by Lean) |
| Section11ShiftBudgetOptimization.lean | `SteklovAudit.cubic_nonnegative` | NOT CHECKED (name not found by Lean) |
| Section11ShiftBudgetOptimization.lean | `SteklovAudit.shift_tradeoff` | NOT CHECKED (name not found by Lean) |
| Section11ShiftedModelSqueeze.lean | `SteklovAudit.asymptotic_squeeze_scalar` | NOT CHECKED (name not found by Lean) |
| Section11ShiftedModelSqueeze.lean | `SteklovAudit.shifted_quadratic_difference` | NOT CHECKED (name not found by Lean) |
| Section11ShrinkingSmoothing.lean | `SteklovAudit.monotone_shift_squeeze` | NOT CHECKED (name not found by Lean) |
| Section11ShrinkingSmoothing.lean | `SteklovAudit.quadratic_shift_right` | NOT CHECKED (name not found by Lean) |
| Section11ShrinkingSmoothing.lean | `SteklovAudit.quadratic_shift_left` | NOT CHECKED (name not found by Lean) |
| Section11SmoothingCounterexample.lean | `SteklovAudit.centered_square_identity` | NOT CHECKED (name not found by Lean) |
| Section11SmoothingCounterexample.lean | `SteklovAudit.shifted_linear_amplitude` | NOT CHECKED (name not found by Lean) |
| Section11ThresholdInstability.lean | `SteklovAudit.threshold_gap_positive` | NOT CHECKED (name not found by Lean) |
| Section11ThresholdInstability.lean | `SteklovAudit.threshold_hs_square` | NOT CHECKED (name not found by Lean) |
| Section11WindowFromSmoothing.lean | `SteklovAudit.quadratic_window_difference` | NOT CHECKED (name not found by Lean) |
| Section11WindowFromSmoothing.lean | `SteklovAudit.window_bound_from_four_sided_squeeze` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.stretch_energy_bounds` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.stretch_inverse_bounds` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.weighted_diag_integrable` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.weighted_diag_integrableOn` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.dyadic_shell_sum` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.inv_le_mul_div_sq` | NOT CHECKED (name not found by Lean) |
| Section4Scalar.lean | `SteklovAudit.Section4Scalar.resolvent_dyadic_bookkeeping` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.cumulative_transfer_telescope` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.transfer_gronwall_bound` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.fixed_time_step_budget` | NOT CHECKED (name not found by Lean) |
| Section7CumulativeTransfer.lean | `SteklovAudit.cumulative_transfer_unbounded` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_diagonal_count` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_shift_energies` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_hs_lower_budget` | NOT CHECKED (name not found by Lean) |
| Section7FixedWindowHSObstruction.lean | `SteklovAudit.fixed_window_no_uniform_hs_budget` | NOT CHECKED (name not found by Lean) |
| Section7IdentificationTraceBudget.lean | `SteklovAudit.identification_budget` | NOT CHECKED (name not found by Lean) |
| Section7IdentificationTraceBudget.lean | `SteklovAudit.identification_budget_mono` | NOT CHECKED (name not found by Lean) |
| Section7LipschitzHSTransfer.lean | `SteklovAudit.square_gap_nonneg` | NOT CHECKED (name not found by Lean) |
| Section7LipschitzHSTransfer.lean | `SteklovAudit.positive_gap_square` | NOT CHECKED (name not found by Lean) |
| Section7OneSidedCountingTransfer.lean | `SteklovAudit.spectral_leakage_budget` | NOT CHECKED (name not found by Lean) |
| Section7OneSidedCountingTransfer.lean | `SteklovAudit.counting_transfer_scalar` | NOT CHECKED (name not found by Lean) |
| Section7OneSidedCountingTransfer.lean | `SteklovAudit.two_sided_counting_scalar` | NOT CHECKED (name not found by Lean) |
| Section7RankLeakage.lean | `SteklovAudit.spectral_gap_square` | NOT CHECKED (name not found by Lean) |
| Section7RankLeakage.lean | `SteklovAudit.leakage_budget` | NOT CHECKED (name not found by Lean) |
| Section7TraceRankAmplification.lean | `SteklovAudit.trace_budget_scalar` | NOT CHECKED (name not found by Lean) |
| Section7TraceRankAmplification.lean | `SteklovAudit.trace_budget_saturation` | NOT CHECKED (name not found by Lean) |
| Section7TraceRankAmplification.lean | `SteklovAudit.trace_budget_quadratic` | NOT CHECKED (name not found by Lean) |
| Section7WeightedLeakage.lean | `SteklovAudit.weighted_gap_square` | NOT CHECKED (name not found by Lean) |
| Section7WeightedLeakage.lean | `SteklovAudit.weighted_tail_bound` | NOT CHECKED (name not found by Lean) |
| Section9NearResonanceObstruction.lean | `SteklovAudit.resonant_defect_identity` | NOT CHECKED (name not found by Lean) |
| Section9NearResonanceObstruction.lean | `SteklovAudit.exact_resonance_zero_defect` | NOT CHECKED (name not found by Lean) |
| Section9NearResonanceObstruction.lean | `SteklovAudit.small_gap_unit_identification` | NOT CHECKED (name not found by Lean) |
| Section9NearResonanceObstruction.lean | `SteklovAudit.resonant_entry_decomposition` | NOT CHECKED (name not found by Lean) |
| Section9NearResonanceObstruction.lean | `SteklovAudit.near_resonance_upper_defect` | NOT CHECKED (name not found by Lean) |
| Section9SpectralGapLeakage.lean | `SteklovAudit.spectral_gap_entry_identity` | NOT CHECKED (name not found by Lean) |
| Section9SpectralGapLeakage.lean | `SteklovAudit.spectral_gap_entry_budget` | NOT CHECKED (name not found by Lean) |
| Section9SpectralGapLeakage.lean | `SteklovAudit.spectral_gap_finite_budget` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.sinh_ne` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.endpoint_eigen_plus` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.endpoint_eigen_minus` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.multiplier_sum` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.multiplier_diff` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.rank_one_weight` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.coth_strictAnti` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.tanh_lt_tanh` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.even_pos` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.odd_neg` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.parity_trace_sum` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.coth_form` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.abs_parity_sum` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.tendsto_sinh_div` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.integrand_tendsto_zero` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.gamma_reflection_imag` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.norm_identity_constant` | NOT CHECKED (name not found by Lean) |
| SectorTrace.lean | `SteklovAudit.SectorTrace.dihedralCoeff_coth_form` | NOT CHECKED (name not found by Lean) |
| SharpLawTransfer.lean | `SteklovAudit.SharpLawTransfer.poly_shift` | NOT CHECKED (name not found by Lean) |
| SharpLawTransfer.lean | `SteklovAudit.SharpLawTransfer.sharp_law_transfer` | NOT CHECKED (name not found by Lean) |
| SharpLawUnique.lean | `SteklovAudit.SharpLawUnique.zero_of_forall_le` | NOT CHECKED (name not found by Lean) |
| SharpLawUnique.lean | `SteklovAudit.SharpLawUnique.diff_small` | NOT CHECKED (name not found by Lean) |
| SharpLawUnique.lean | `SteklovAudit.SharpLawUnique.sharp_law_unique` | NOT CHECKED (name not found by Lean) |
| SharpLawUnique.lean | `SteklovAudit.SharpLawUnique.edge_invariant_determined` | NOT CHECKED (name not found by Lean) |
| SharpLawUnique.lean | `SteklovAudit.SharpLawUnique.not_one_term_law` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.window_gap_leakage` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.weighted_leakage` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.counting_transfer` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.swap_K_sq` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.counting_two_sided` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.threshold_instability` | NOT CHECKED (name not found by Lean) |
| SpectralCounting.lean | `SteklovAudit.AbstractTransfer.trace_rank_amplification` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.le_of_deriv_nonpos` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.le_of_deriv_nonneg` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.hasDerivAt_aux` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.taylor_upper` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.taylor_lower` | NOT CHECKED (name not found by Lean) |
| TaylorRemainder.lean | `SteklovAudit.TaylorRemainder.taylor_remainder_of_lipschitz_deriv` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.face_midpoint_moments` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.boundary_mass` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.green_pair` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.residual_orthogonal` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.residual_energy` | NOT CHECKED (name not found by Lean) |
| TetraAffineFlux.lean | `SteklovAudit.TetraAffineFlux.cutoff_tail_moment` | NOT CHECKED (name not found by Lean) |
| TetraAssemblyFace.lean | `SteklovAudit.TetraAssemblyFace.tetra_law_of_face_and_edges` | NOT CHECKED (name not found by Lean) |
| TetraAssemblyFace.lean | `SteklovAudit.TetraAssemblyFace.tetra_law_of_overlap_and_face` | NOT CHECKED (name not found by Lean) |
| TetraAssemblyFace.lean | `SteklovAudit.TetraAssemblyFace.tetra_law_equal_edges` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.sqrt_littleO` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.wsq_pos` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.witness_edge_laws` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.witness_overlap` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.witness_nonvacuous` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawNonvacuous.lean | `SteklovAudit.TetraEdgeLawNonvacuous.witness_conclusion` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawOverlap.lean | `SteklovAudit.TetraEdgeLawOverlap.tetra_edge_law_of_overlap` | NOT CHECKED (name not found by Lean) |
| TetraEdgeLawOverlap.lean | `SteklovAudit.TetraEdgeLawOverlap.overlap_must_shrink` | NOT CHECKED (name not found by Lean) |
| TraceLocalMass.lean | `SteklovAudit.TraceLocalMass.trace_cs` | NOT CHECKED (name not found by Lean) |
| TraceLocalMass.lean | `SteklovAudit.TraceLocalMass.trace_local_mass_le` | NOT CHECKED (name not found by Lean) |
| TraceLocalMass.lean | `SteklovAudit.TraceLocalMass.littleO_of_bounded_defect` | NOT CHECKED (name not found by Lean) |
| TraceLocalMass.lean | `SteklovAudit.TraceLocalMass.hs2_zero_array` | NOT CHECKED (name not found by Lean) |
| TraceLocalMassGrowth.lean | `SteklovAudit.TraceLocalMassGrowth.littleO_of_growing_lipschitz` | NOT CHECKED (name not found by Lean) |
| TraceLocalMassGrowth.lean | `SteklovAudit.TraceLocalMassGrowth.growing_needs_rate` | NOT CHECKED (name not found by Lean) |
| TraceLocalMassGrowth.lean | `SteklovAudit.TraceLocalMassGrowth.growing_needs_rate_not_littleO` | NOT CHECKED (name not found by Lean) |
| TraceLocalMassGrowth.lean | `SteklovAudit.TraceLocalMassGrowth.trace_littleO_of_growth` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.abs_trace_le_sum_abs_diag` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.trace_diagonal_mul` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.abs_signDiag_le` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.signDiag_mul` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.sum_abs_diag_le_of_dual` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.dual_at_diag` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.identification_budget_traceNorm` | NOT CHECKED (name not found by Lean) |
| TraceNormBudget.lean | `SteklovAudit.TraceNormBudget.identification_budget_diag` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.tri_int_one` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.tri_int_s` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.tri_int_ss` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.tri_int_st` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.midpoint_rule_exact_deg2` | NOT CHECKED (name not found by Lean) |
| TriangleQuadrature.lean | `SteklovAudit.TriangleQuadrature.midpoint_eq_integral` | NOT CHECKED (name not found by Lean) |
| TwoParameterSmoothing.lean | `SteklovAudit.TwoParameterSmoothing.error_budget` | NOT CHECKED (name not found by Lean) |
| TwoParameterSmoothing.lean | `SteklovAudit.TwoParameterSmoothing.sharp_law_of_two_parameter_smoothing` | NOT CHECKED (name not found by Lean) |
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
| VertexLog.lean | `SteklovAudit.VertexLog.log_le_two_sqrt` | NOT CHECKED (name not found by Lean) |
| VertexLog.lean | `SteklovAudit.VertexLog.vertex_of_log` | NOT CHECKED (name not found by Lean) |
| VertexLog.lean | `SteklovAudit.VertexLog.theorem_11_1_of_D5` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.channel_sum` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.channel_difference` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.sinh_le_mul_cosh` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.mul_cosh_le` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.tanh_le_id` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.div_one_add_le_tanh` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.inv_le_coth` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.coth_le_one_add_inv` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.m_mul_inv` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.sym_lower` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.sym_upper` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.anti_lower` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.anti_upper` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.channel_lower` | NOT CHECKED (name not found by Lean) |
| WedgeChannel.lean | `SteklovAudit.WedgeChannel.antisym_physical` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweighted.lean | `SteklovAudit.WeightedToUnweighted.main_terms_agree` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweighted.lean | `SteklovAudit.WeightedToUnweighted.unweighted_of_weighted` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweighted.lean | `SteklovAudit.WeightedToUnweighted.weighted_gap_must_shrink` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweightedNonvacuous.lean | `SteklovAudit.WeightedToUnweightedNonvacuous.witness_gap` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweightedNonvacuous.lean | `SteklovAudit.WeightedToUnweightedNonvacuous.witness_gap_ne` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweightedNonvacuous.lean | `SteklovAudit.WeightedToUnweightedNonvacuous.witness_hyps` | NOT CHECKED (name not found by Lean) |
| WeightedToUnweightedNonvacuous.lean | `SteklovAudit.WeightedToUnweightedNonvacuous.witness_conclusion` | NOT CHECKED (name not found by Lean) |
| WindowBoundedNonvacuous.lean | `SteklovAudit.WindowBoundedNonvacuous.window_witness_bound` | NOT CHECKED (name not found by Lean) |
| WindowBoundedNonvacuous.lean | `SteklovAudit.WindowBoundedNonvacuous.window_witness_ne` | NOT CHECKED (name not found by Lean) |
| WindowBoundedNonvacuous.lean | `SteklovAudit.WindowBoundedNonvacuous.window_bounded_nonvacuous` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.int_bounds` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.Hc_increment` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.strip_trace_increment` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.lorentz_integral_le` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.band_resolvent_integral` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.off_band_gap` | NOT CHECKED (name not found by Lean) |
| WindowBounds.lean | `SteklovAudit.WindowBounds.off_band_absorb` | NOT CHECKED (name not found by Lean) |
| WindowDefectFullTrace.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.fullTraceSmall_of_window` | NOT CHECKED (name not found by Lean) |
| WindowDefectFullTrace.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.h5_of_cutoff_window` | NOT CHECKED (name not found by Lean) |
| WindowDefectFullTrace.lean | `SteklovAudit.H5CutoffInterface.H5EdgeFamilyCutoff.windowTraceBound_of_trace_zero` | NOT CHECKED (name not found by Lean) |
| WindowLocalMassBounded.lean | `SteklovAudit.WindowLocalMassBounded.sqrt_local_mass_eq` | NOT CHECKED (name not found by Lean) |
| WindowLocalMassBounded.lean | `SteklovAudit.WindowLocalMassBounded.eps_of_bounded_small` | NOT CHECKED (name not found by Lean) |
| WindowLocalMassBounded.lean | `SteklovAudit.WindowLocalMassBounded.littleO_of_window_bounded_defect` | NOT CHECKED (name not found by Lean) |
| WindowLocalMassBounded.lean | `SteklovAudit.WindowLocalMassBounded.local_mass_rate_needed` | NOT CHECKED (name not found by Lean) |

## Build errors

```
error: SteklovAudit/WindowBoundedNonvacuous.lean:44:11: Unknown identifier `le_or_lt`
error: SteklovAudit/WindowBoundedNonvacuous.lean:44:29: Tactic `rcases` failed: `x✝ : ?m.184` is not an inductive datatype
error: build failed
```

## Lean output

```
/home/runner/work/steklov-lean/steklov-lean/AxiomAudit.lean:1:0: error: object file '/home/runner/work/steklov-lean/steklov-lean/.lake/build/lib/lean/SteklovAudit/WindowBoundedNonvacuous.olean' of module SteklovAudit.WindowBoundedNonvacuous does not exist

```
