import numpy as np
from sklearn.cluster import DBSCAN

def dbscan(points, eps=50, min_samples=2):
    if points == []:
        return []
    # Extract x and y coordinates from the input points
    X = np.array([[point[1], point[2]] for point in points])
    
    # Create and fit DBSCAN model
    dbscan = DBSCAN(eps=eps, min_samples=min_samples)
    dbscan.fit(X)
    
    # Get cluster labels
    labels = dbscan.labels_
    
    # Create result list
    result = [[points[i][0], label] for i, label in enumerate(labels)]
    
    return result
