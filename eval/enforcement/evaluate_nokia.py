from evaluation import run_experiments


run_experiments(
    option        = 'lifeboat',
    benchmark     = 'nokia',
    exe           = './lifeboat.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
)

run_experiments(
    option        = 'monpoly',
    benchmark     = 'nokia',
    exe           = './monpoly.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
)

run_experiments(
    option        = 'enfpoly',
    benchmark     = 'nokia',
    exe           = './enfpoly.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
)

run_experiments(
    option        = 'whyenf',
    benchmark     = 'nokia',
    exe           = './whyenf.exe',
    accelerations = [1, 2, 4, 8, 16, 32, 64, 128, 256],
    n             = 1,#10,
    time_unit     = 1,
)

