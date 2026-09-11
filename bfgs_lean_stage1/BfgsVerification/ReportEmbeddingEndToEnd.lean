import BfgsVerification.ReportEmbeddingTargets

noncomputable section
namespace BfgsVerification.DEmbedding

theorem objectiveGeometry : ObjectiveGeometryTarget := objective_function_contract

theorem embeddingFailure : EmbeddingFailureTarget := deterministic_embedding_failure

end BfgsVerification.DEmbedding
namespace BfgsVerification.LQuadraticSeed

theorem quadraticSeed : QuadraticSeedTarget := fun _ hμ => quadratic_seed_contract hμ

end BfgsVerification.LQuadraticSeed
