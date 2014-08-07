from collections import namedtuple

Stats = namedtuple('Stats', 'min max mean weight')

def stats(counter):
    if len(counter) == 0:
        return Stats(min=None, max=None, mean=None, weight=0)
    min = max = counter.iterkeys().next()
    samples = weight = 0
    for weight, count in counter.iteritems():
        if weight < min:
            min = weight
        elif weight > max:
            max = weight
        samples += count
        weight += weight * count
    return Stats(min=min, max=max, mean=weight / float(samples), weight=weight)

def to_line(counter, width = 72, right = None, label = True):
    st = stats(counter)
    if st.min == None:
        return " " * width
    CHARS = map(unichr, range(0x2581, 0x2589))
    left = min(0, st.min)
    if right is None:
        right = max(0, st.max)
    if left == right:
        return "%s %s %s" % (st.min, CHARS[-1], st.max)
    leftLabel = (str(left) + " ") if label and left != 0 else ""
    rightLabel = (" " + str(right)) if label and right != 0 else ""
    width = max(width - len(leftLabel) - len(rightLabel), 1)
    bucket_width = float(right - left) / width
    buckets = [0] * width
    for weight, count in counter.items():
        buckets[min(int((weight - left) / bucket_width),
                    width - 1)] += count
    maxbucket = max(buckets)
    res = []
    for b in buckets:
        if b == 0:
            res.append(u" ")
        else:
            res.append(CHARS[min(b * len(CHARS) / maxbucket, len(CHARS)-1)])
    return "%s%s%s" % (leftLabel, "".join(res), rightLabel)
