from evaluation import run_experiments

run_experiments(
    option        = 'lifeboat',
    benchmark     = 'gdpr',
    exe           = './lifeboat.exe',
    accelerations = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7],
    n             = 1,#10,
    time_unit     = 24 * 3600
)

run_experiments(
    option        = 'whyenf',
    benchmark     = 'gdpr',
    exe           = './whyenf.exe',
    accelerations = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7],
    n             = 1,#10,
    time_unit     = 24 * 3600,
    to            = 300,
    only_graph    = True
)

run_experiments(
    option        = 'enfpoly',
    benchmark     = 'gdpr',
    exe           = './enfpoly.exe',
    accelerations = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7],
    n             = 1,#10,
    time_unit     = 24 * 3600
)