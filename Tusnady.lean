import Tusnady.Definitions
import Tusnady.Literature
import Tusnady.DyadicGeometry
import Tusnady.DyadicIntervals
import Tusnady.DyadicCells
import Tusnady.EntropyTransfer
import Tusnady.Gini
import Tusnady.Padding
import Tusnady.ErrorEstimates
import Tusnady.EntropyAggregation
import Tusnady.MixedSampling
import Tusnady.GaussianCover
import Tusnady.DyadicFunctionsGeometry
import Tusnady.GaussianMarginals
import Tusnady.GramResponse
import Tusnady.ConditionedGaussianFinite
import Tusnady.EntropyDensityConditional
import Tusnady.SmoothedBlockLinear
import Tusnady.TestFunctionIntegrals
import Tusnady.CellAnalytic
import Tusnady.PrimitiveDuality
import Tusnady.HaarFiniteCombination
import Tusnady.CellLocation
import Tusnady.SamplingSpaceCounting
import Tusnady.SamplingDomainBasis
import Tusnady.ConditionedGaussianObstruction
import Tusnady.PointGaussianBody
import Tusnady.UniformMonomial
import Tusnady.SparseMixedDistinct
import Tusnady.SamplingPrimitiveInclusion
import Tusnady.ShellHilbert
import Tusnady.ShellHighProjection
import Tusnady.RemainderSamplingScalar
import Tusnady.RemainderRelative
import Tusnady.ResponseScale
import Tusnady.TestResponse
import Tusnady.FinalTransfer
import Tusnady.MainWitness
import Tusnady.CellShellSets
import Tusnady.TestResponseFintype
import Tusnady.LiteratureRosenblattScalar
import Tusnady.PrekopaBrunnMinkowski1D
import Tusnady.PrekopaLayerCake
import Tusnady.PrekopaDecay
import Tusnady.LiteratureSamplingBasic
import Tusnady.LiteratureSamplingFiniteApprox
import Tusnady.LiteratureSamplingGramApprox
import Tusnady.LiteratureRosenblatt
import Tusnady.FrameBasic

import Tusnady.LiteratureAnderson

import Tusnady.LiteratureEntropyChain

import Tusnady.MainLiterature

import Tusnady.MainUnconditional

/-!
The higher-dimensional lower bound from Main.pdf Theorem 1.1, proved without
unproved literature or construction premises.

`Tusnady.main_lower_bound_unconditional : Tusnady.HigherDimensionalLowerBound`.
All five original literature statements are proved in `LiteratureProof`.
Run `scripts/check.sh --complete` for the actual declaration-type check and
exhaustive recursive axiom audit. `--conditional` preserves the first-stage
conditional statement as a separate historical check.
-/
