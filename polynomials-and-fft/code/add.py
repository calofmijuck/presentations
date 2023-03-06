from typing import List
from math import sin, cos, pi

def add(f: List[int], g: List[int]) -> List[int]:
    return [f[i] + g[i] for i in range(len(f))]

def multiply(f: List[int], g: List[int]) -> List[int]:
    product = [0] * (len(f) + len(g))
    for i in range(len(product)):
        for j in range(i + 1):
            product[i] += f[i] * g[j - i]
    return product

# Assuming len(f) is a power of 2
def fft(f: List[complex]) -> List[complex]:
    n = len(f)
    if n <= 1:
        return f

    f_even, f_odd = f[::2], f[1::2]
    fft_even, fft_odd = fft(f_even), fft(f_odd)

    result = [0] * n
    for i in range(n // 2):
        omega = complex(cos(2 * pi / n), sin(2 * pi / n)) ** i

        result[i] = fft_even[i] + omega * fft_odd[i]
        result[i + n // 2] = fft_even[i] - omega * fft_odd[i]

    return result

# Assuming len(f) is a power of 2
def inverse_fft(f: List[complex]) -> List[complex]:
    n = len(f)
    if n <= 1:
        return f

    f_even, f_odd = f[::2], f[1::2]
    inverse_fft_even, inverse_fft_odd = inverse_fft(f_even), inverse_fft(f_odd)

    result = [0] * n
    for i in range(n // 2):
        omega = complex(cos(2 * pi / n), sin(2 * pi / n)) ** -i

        result[i] = inverse_fft_even[i] + omega * inverse_fft_odd[i]
        result[i + n // 2] = inverse_fft_even[i] - omega * inverse_fft_odd[i]

    return [result_i / 2 for result_i in result]



f = fft([1, 2, 3, 4, 5, 6, 7, 8])

print(f)

res = inverse_fft(f)

print(res)
