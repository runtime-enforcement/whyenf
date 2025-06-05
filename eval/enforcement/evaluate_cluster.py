from evaluation import run_experiments

run_experiments(
    option        = 'enfguard',
    benchmark     = 'cluster',
    exe           = './enfguard.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
    func          = True,
    only_graph    = True,
)
