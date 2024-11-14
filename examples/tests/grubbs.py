import numpy as np
from scipy import stats

def GRUBBS(data):
    # Extract values and keys
    values = np.array([v for k, v in data])
    keys = [k for k, v in data]
    
    n = len(values)

    if n == 0:
        return []
    elif n == 1:
        return [(keys[0], 0)]

    # Calculate mean and standard deviation
    mean = np.mean(values)
    std = np.std(values, ddof=1)
    
    # Calculate G-statistic for each value
    G = np.abs(values - mean) / std
    
    # Calculate critical value
    t_crit = stats.t.ppf(1 - 0.05 / (2 * n), n - 2)
    G_crit = ((n - 1) / np.sqrt(n)) * np.sqrt(t_crit**2 / (n - 2 + t_crit**2))
    
    # Identify outliers
    is_outlier = G > G_crit
    
    # Create result sequence
    result = [(k, int(outlier)) for k, outlier in zip(keys, is_outlier)]
    
    return result
