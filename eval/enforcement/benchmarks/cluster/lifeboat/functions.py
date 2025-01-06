import numpy as np
from scipy import stats # type: ignore
from sklearn.cluster import DBSCAN as D # type: ignore

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

def DBSCAN(data):
    # Extract values and keys
    values = np.array([v for k, v in data])
    keys = [k for k, v in data]
    
    n = len(values)

    if n == 0:
        return []
    elif n == 1:
        return [(keys[0], 0)]

    # Reshape values for DBSCAN
    X = values.reshape(-1, 1)

    # Apply DBSCAN
    dbscan = D(eps=0.5, min_samples=2)
    labels = dbscan.fit_predict(X)

    # Identify outliers (points labeled as -1 are considered outliers)
    is_outlier = labels == -1

    # Create result sequence
    result = [(k, int(outlier)) for k, outlier in zip(keys, is_outlier)]
    
    return result
