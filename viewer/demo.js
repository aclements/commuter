var database = new Database();

$(document).ready(function() {
    var qc = new QueryCanvas($('#container'), database.outputRv);
    qc.heatmap(Predicate.conflicted,
               function(tc) { return tc.runid; });
    qc.heatbar(Predicate.conflicted);
    qc.table(function(tc) {
        // Lazy load detail databases
        if (!database.loadMscan('data/' + tc.runid + '-details.json'))
            return $('<span>').text('Loading details...');
    });

    database.loadMscan('data/sv6.json');
    database.loadMscan('data/Linux.json');
});
