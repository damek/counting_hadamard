# RequestProject

`RequestProject/` is the active Lean development.

Read it in this order:

1. `HadamardCn3.lean`
   The curated public entrypoint. It re-exports the endpoint theorem file,
   the weak invariance input, and the one nontrivial paper-notation bridge.

2. `HadamardCn3ShortMain.lean`
   The count theorem file. It exposes only the count-side
   quantities used in the final statements:
   - `paperCount n s = N_{n,s}`
   - `paperAsymptoticCount n t = A_{n,4t}`
   and then states the endpoint theorems:
   - `thm_main_intro`
   - `cor_uniform`

3. `HadamardCn3Asymptotics.lean`
   The intermediate normalized-count statements:
   - `paperNormalizedCount`
   - `paperTargetIntegral`
   - `paperNormalizedIntegral`
   - `paperMainScale`
   - `paperMainTerm`
   - `paperNormalizedCount_eq_integral`
   - `prop_primary_box`
   - `normalizedCount_asymptotic`

4. Split foundational layer
   Read the foundational modules in this order:
   - `HadamardCn3Defs.lean`
     Basic combinatorial and Gaussian definitions.
   - `HadamardCn3TorusCount.lean`
     Torus/count bridge and Fourier inversion surface.
   - `HadamardCn3Moments.lean`
     Reusable Gaussian moment estimates.
   - `HadamardCn3DiscreteMoments.lean`
     Reusable discrete sign-moment identities and quintic pointwise bounds.
   - `HadamardCn3MOO.lean`
     MOO / influence quantities and the base weak-invariance support.
   - `HadamardCn3ResidualBase.lean`
     Triangle/quartic/cubic residual-support layer.

5. `HadamardCn3WeakInvariance.lean`
   The weak Mossel-O'Donnell-Oleszkiewicz invariance input:
   - `quadraticForm_lindeberg_comparison_C3`
   - `psi_sub_gaussianPsi_le_threeHalfInfluenceSum`

6. `HadamardCn3PaperSpec.lean`
   Keeps only the paper-specific renormalization theorem
   `paper_threeHalfInfluenceSum_eq_eight_kernelInfluence_sum`.

7. `HadamardCn3QuarticFiber.lean`
   The quartic Gaussian perturbation estimates used inside the local-gap proof.

8. `HadamardCn3LocalGapBridge.lean`
   The main local-gap bridge from the exact core to the cubic/Gaussian model.

9. `HadamardCn3LocalGapResidual.lean`
   The residual estimate.

10. `HadamardCn3LocalGapFixedN.lean`
   The fixed-`n` fallback endpoint:
   - `fixed_n_count_asymptotic`

11. `HadamardCn3LocalGapCore.lean` and `HadamardCn3LocalGap.lean`
   Thin import aggregators.

The repository umbrella module is `RequestProject.lean`.
