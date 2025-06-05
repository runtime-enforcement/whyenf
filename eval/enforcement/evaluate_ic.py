from evaluation import run_experiments

run_experiments(
    option        = 'monpoly',
    benchmark     = 'ic',
    exe           = './monpoly.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],    
    n             = 1,#10,
    time_unit     = 1,

    #only_graph    = True,
)

run_experiments(
    option        = 'lifeboat',
    benchmark     = 'ic',
    exe           = './lifeboat.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
    #only_graph     = True
)
