#!/usr/bin/env python3
"""
Recolor the act logo to match the mustard yellow from the website banner.
"""

from PIL import Image
import numpy as np

# Load the image
input_path = "src/images/logo/logo_bg[ylw]_fg[blk]_v01.png"
output_path = "src/images/logo/logo_bg[mustard]_fg[blk]_v01.png"

img = Image.open(input_path).convert("RGBA")
data = np.array(img)

# Get RGB and alpha channels
red, green, blue, alpha = data.T

# Target color from the banner (approximately)
target_color = (200, 148, 70)  # #C89446

# Find yellow pixels (assuming current logo is bright yellow)
# Adjust these thresholds if needed
yellow_areas = (red > 200) & (green > 200) & (blue < 100)

# Replace yellow with mustard color
data[..., :-1][yellow_areas.T] = target_color

# Create new image
img_recolored = Image.fromarray(data)
img_recolored.save(output_path)

print(f"Recolored logo saved to: {output_path}")
