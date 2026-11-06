import Tusnady.Upper.Main
import Tusnady.Upper.Ehrhard.VerticalFoldMonotonicity
import Tusnady.Upper.Ehrhard.SmallFoldClosure
import Tusnady.Upper.Ehrhard.PlanarFoldComparison
import Tusnady.Upper.Ehrhard.PlanarReductionData
import Tusnady.Upper.CompactGaussianBody
import Tusnady.Upper.Conclusions
import Tusnady.Upper.DyadicFactorization
import Tusnady.Upper.DyadicFactorizationLog
import Tusnady.Upper.DyadicFactorizationRanks
import Tusnady.Upper.DyadicFactorizationTensor
import Tusnady.Upper.DyadicFactorizationTree
import Tusnady.Upper.Ehrhard.AffineSoftMinimum
import Tusnady.Upper.Ehrhard.ClosedBallApproximation
import Tusnady.Upper.Ehrhard.ConeTranslation
import Tusnady.Upper.Ehrhard.ConvexApproximation
import Tusnady.Upper.Ehrhard.ConvexConcavity
import Tusnady.Upper.Ehrhard.ConvexLift
import Tusnady.Upper.Ehrhard.CoordinateConcavity
import Tusnady.Upper.Ehrhard.CoordinateSections
import Tusnady.Upper.Ehrhard.FoldRotation
import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics
import Tusnady.Upper.Ehrhard.GaussianBase
import Tusnady.Upper.Ehrhard.GaussianConvexOrigin
import Tusnady.Upper.Ehrhard.GaussianIsoperimetry
import Tusnady.Upper.Ehrhard.GaussianPlane
import Tusnady.Upper.Ehrhard.GaussianRotation
import Tusnady.Upper.Ehrhard.GaussianScalar
import Tusnady.Upper.Ehrhard.GaussianSections
import Tusnady.Upper.Ehrhard.GaussianTailBounds
import Tusnady.Upper.Ehrhard.HalfplaneFold
import Tusnady.Upper.Ehrhard.HeatConvolution
import Tusnady.Upper.Ehrhard.HeatMaximum
import Tusnady.Upper.Ehrhard.HeatTransport
import Tusnady.Upper.Ehrhard.Minkowski
import Tusnady.Upper.Ehrhard.ModifiedFoldContainment
import Tusnady.Upper.Ehrhard.ModifiedFoldPlanar
import Tusnady.Upper.Ehrhard.ModifiedFoldSymmetrization
import Tusnady.Upper.Ehrhard.ModifiedVerticalFold
import Tusnady.Upper.Ehrhard.PlanarCap
import Tusnady.Upper.Ehrhard.PlanarSupport
import Tusnady.Upper.Ehrhard.PlanarSymmetrization
import Tusnady.Upper.Ehrhard.PlanarSymmetrizationClosed
import Tusnady.Upper.Ehrhard.PlanarSymmetrizationData
import Tusnady.Upper.Ehrhard.PolyhedralApproximation
import Tusnady.Upper.Ehrhard.PolyhedralConcavity
import Tusnady.Upper.Ehrhard.ProjectionApproximation
import Tusnady.Upper.Ehrhard.Quantile
import Tusnady.Upper.Ehrhard.QuantileCalculus
import Tusnady.Upper.Ehrhard.SmallRadiusQuantile
import Tusnady.Upper.Ehrhard.SmoothedConcavity
import Tusnady.Upper.Ehrhard.SoftMinimum
import Tusnady.Upper.Ehrhard.Stein
import Tusnady.Upper.Ehrhard.Symmetrization
import Tusnady.Upper.Ehrhard.SymmetrizationClosed
import Tusnady.Upper.Ehrhard.Translation
import Tusnady.Upper.GaussianBody
import Tusnady.Upper.GaussianConcentration
import Tusnady.Upper.GaussianThreshold
import Tusnady.Upper.LogComparison
import Tusnady.Upper.NikolovReduction
import Tusnady.Upper.NikolovSmallRadiusReduction
import Tusnady.Upper.OrthantPrefixBalancing
import Tusnady.Upper.OrthantPrefixFactorization
import Tusnady.Upper.OrthantPrefixGeometry
import Tusnady.Upper.OrthantPrefixTransfer
import Tusnady.Upper.PrefixBalancing
import Tusnady.Upper.PrefixFoldGeometry
import Tusnady.Upper.PrefixGaussian
import Tusnady.Upper.PrefixGaussianOneDimensional
import Tusnady.Upper.PrefixSmallRadius
import Tusnady.Upper.Statements

/-!
Nikolov's upper bound and the sharp order are proved unconditionally in
`Tusnady.Upper.Main`. The proof uses the proved universal signing factor 1000.
Historical conditional reductions keep their premises explicit and are audited
as implications. `scripts/check-upper.sh --complete` checks the four exact
unconditional target types, their recursive standard-axiom dependencies, and
the unchanged complete lower-bound audit.
-/
