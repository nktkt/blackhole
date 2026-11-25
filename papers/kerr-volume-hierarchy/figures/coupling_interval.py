"""Draw the dimensionless Kerr coupling bounds used in the paper."""

from math import sqrt
from pathlib import Path

import reportlab
from reportlab.lib.colors import HexColor
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas


def bounds(spin):
    squared = spin * spin
    factor = 1 + squared
    lower = -squared * (3 + 2 * squared) / (12 * factor)
    upper = squared**2 / (12 * factor * (sqrt(factor) + 1) ** 2)
    return lower, upper


def draw_panel(canvas, left, right, low, high, ticks, upper_only=False):
    bottom, top = 39, 158
    ink, grid = HexColor("#202D36"), HexColor("#D9E0E3")
    lower_color, upper_color = HexColor("#166463"), HexColor("#A14424")

    def project(spin, value):
        return left + spin * (right - left), bottom + (value - low) / (high - low) * (top - bottom)

    spins = [index / 240 for index in range(241)]
    lower_points = [project(spin, bounds(spin)[0]) for spin in spins]
    upper_points = [project(spin, bounds(spin)[1]) for spin in spins]

    def path_through(points):
        line = canvas.beginPath()
        line.moveTo(*points[0])
        for point in points[1:]:
            line.lineTo(*point)
        return line

    if not upper_only:
        band = path_through(lower_points + upper_points[::-1])
        band.close()
        canvas.setFillColor(HexColor("#D6EAE5"))
        canvas.drawPath(band, stroke=0, fill=1)

    canvas.setFont("Vera", 8.7)
    for value, label in ticks:
        _, y = project(0, value)
        canvas.setStrokeColor(grid)
        canvas.setLineWidth(0.45)
        canvas.line(left, y, right, y)
        canvas.setFillColor(ink)
        canvas.drawRightString(left - 5, y - 3, label)
    canvas.setStrokeColor(ink)
    canvas.setLineWidth(0.7)
    canvas.line(left, bottom, right, bottom)
    canvas.line(left, bottom, left, top)
    for spin, label in [(0, "0"), (0.25, "0.25"), (0.5, "0.5"), (0.75, "0.75"), (1, "1")]:
        x, _ = project(spin, low)
        canvas.line(x, bottom, x, bottom - 3)
        canvas.drawCentredString(x, bottom - 14, label)

    if not upper_only:
        canvas.setStrokeColor(lower_color)
        canvas.setLineWidth(1.65)
        canvas.drawPath(path_through(lower_points))
    canvas.setStrokeColor(upper_color)
    canvas.setLineWidth(1.65)
    canvas.setDash(4, 2)
    canvas.drawPath(path_through(upper_points))
    canvas.setDash()
    endpoints = [(upper_points[-1], upper_color)]
    if not upper_only:
        endpoints.append((lower_points[-1], lower_color))
    for (x, y), color in endpoints:
        canvas.setStrokeColor(color)
        canvas.setFillColor(HexColor("#FFFFFF"))
        canvas.setLineWidth(1.15)
        canvas.circle(x, y, 2.0, fill=1)

    canvas.setFillColor(ink)
    canvas.setFont("Vera Bold", 10.8)
    canvas.drawString(left, 169, "Upper endpoint" if upper_only else "Full interval")
    canvas.setFont("Vera", 9)
    canvas.drawCentredString((left + right) / 2, 8, "Absolute spin")


def main():
    fonts = Path(reportlab.__file__).parent / "fonts"
    pdfmetrics.registerFont(TTFont("Vera", str(fonts / "Vera.ttf")))
    pdfmetrics.registerFont(TTFont("Vera Bold", str(fonts / "VeraBd.ttf")))
    target = Path(__file__).with_name("coupling-interval.pdf")
    canvas = Canvas(str(target), pagesize=(490, 184), invariant=1, pageCompression=1,
                    initialFontName="Vera")
    canvas.setTitle("Allowed Kerr coupling versus absolute spin")
    canvas.setAuthor("Naoki Takata")
    draw_panel(canvas, 53, 250, -0.22, 0.021,
               [(-0.2, "−0.20"), (-0.15, "−0.15"), (-0.1, "−0.10"), (-0.05, "−0.05"), (0, "0")])
    draw_panel(canvas, 314, 483, -0.0002, 0.0082,
               [(0, "0"), (0.002, "0.002"), (0.004, "0.004"), (0.006, "0.006"), (0.008, "0.008")],
               upper_only=True)
    canvas.saveState()
    canvas.setFillColor(HexColor("#202D36"))
    canvas.setFont("Vera", 9)
    canvas.translate(9, 99)
    canvas.rotate(90)
    canvas.drawCentredString(0, 0, "Normalized coupling")
    canvas.restoreState()
    canvas.showPage()
    canvas.save()


if __name__ == "__main__":
    main()
