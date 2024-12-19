from evaluation import run_experiments

run_experiments(
    option        = 'lifeboat',
    benchmark     = 'agg',
    exe           = './lifeboat.exe',
    accelerations = [1],
    n             = 1,#10,
    time_unit     = 1,
    only_graph = True
)