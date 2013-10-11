var database;

$(document).ready(function() {
    database = new Database($('#container'));
    var qc = new QueryCanvas($('#container'), database.outputRv);
    qc.heatmap(Predicate.conflicted,
               function(tc) { return tc.runid; });
    qc.heatbar(Predicate.conflicted);

    // Disable the following when not using separate details databases
    qc.table(function(tc) {
        // Lazy load detail databases
        if (!database.loadMscan('data/' + tc.runid + '-details.json'))
            return $('<span>').text('Loading details...');
    });

    // Load main mscan databases
    database.loadMscan('data/sv6.json');
    database.loadMscan('data/Linux.json');
});
