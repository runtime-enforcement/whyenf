from evaluation import run_experiments

run_experiments(
    option        = 'lifeboat',
    benchmark     = 'ic',
    exe           = './lifeboat.exe',
    accelerations = [1],
    n             = 1,#10,
    time_unit     = 1,
    to            = 1,
)